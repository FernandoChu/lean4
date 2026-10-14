/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

prelude
public import Lean.CoreM

public section

/-!
# Controlled unfolding

An experimental implementation of controlled unfolding (Gratzer, Sterling, Angiuli, Coquand,
Birkedal, "Controlling unfolding in type theory"), extended with guarded rewrite rules.

The paper elaborates definitions to constants of extension types `{A | Υ_f ↪ δ_f}` over proposition
symbols `Υ_f`. We do not add extension types to the kernel but, as Agda's `opaque` does, instrument
conversion checking: proposition symbols are declaration names, and an *active set* of names is
assumed while a declaration's value is elaborated and kernel-checked. Its type is checked with an
empty active set.

A declaration may carry an `UnfoldPolicy`:
* `@[controlled] def f` makes `f` unfold only where `f` itself is active (the paper's
  `Υ_f ≤ Υ_κ₁ ∧ ⋯`, where the `κᵢ` are the names its value was checked under).
* A declaration whose value is checked under a non-empty active set and that is not `controlled` is
  an *abbreviation* (the paper's `Υ_f = Υ_κ₁ ∧ ⋯`): it unfolds wherever all of those names are
  active, so its value never escapes the scope it was checked in.
* `@[guarded_rewrite] theorem R` is a rewrite rule (see `Lean.RewriteRules`) that only fires where
  `R` is active.

The active set lives in the options under the prefix `_unfolding`, so it is propagated into
terms, tactics, and asynchronous elaboration tasks like any other option. The kernel reads the
policies through the same environment extension, and since a policy can only ever forbid
unfoldings or disable guarded rules, it does not need to trust them.
-/

namespace Lean

structure UnfoldPolicy where
  declName    : Name
  /-- `@[controlled]`; otherwise the declaration is an abbreviation of `requires`. -/
  controlled  : Bool := false
  /-- The active set the declaration's value was checked under. -/
  requires    : Array Name := #[]
  /-- `@[guarded_rewrite]`: the declaration is a rewrite rule that fires only where it is active. -/
  guardedRule : Bool := false
  deriving Inhabited

private def UnfoldPolicies.add (m : NameMap UnfoldPolicy) (p : UnfoldPolicy) : NameMap UnfoldPolicy :=
  m.insert p.declName p

builtin_initialize unfoldPolicyExt :
    SimplePersistentEnvExtension UnfoldPolicy (NameMap UnfoldPolicy) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := UnfoldPolicies.add
    addImportedFn := mkStateFromImportedEntries UnfoldPolicies.add {}
    -- The kernel reads the state from `Environment.checked`, so modifications must reach it.
    asyncMode     := .sync
    -- Equation lemmas of controlled definitions are added in realization contexts.
    replay?       := some <| SimplePersistentEnvExtension.replayOfFilter
      (fun m p => !m.contains p.declName) UnfoldPolicies.add
  }

/--
Returns the policy of `declName`. By default only the current environment branch is consulted, which
suffices for definitions; policies of theorems may have been recorded on asynchronous branches or in
realizations (e.g. equation lemmas), and need `sync := true`, which blocks on prior branches.
-/
def getUnfoldPolicy? (env : Environment) (declName : Name) (sync := false) : Option UnfoldPolicy :=
  let onBranch := unfoldPolicyExt.getState env (asyncMode := .local)
  -- Policies on other branches all stem from a controlled definition or guarded rule visible
  -- here, so files that do not use the feature never block.
  if !sync || Std.TreeMap.isEmpty onBranch then onBranch.find? declName
  else (unfoldPolicyExt.getState env (asyncMode := .sync)).find? declName

/-- Applies `f` to the policy of `declName`, starting from the default policy if it has none. -/
def modifyUnfoldPolicy (env : Environment) (declName : Name) (f : UnfoldPolicy → UnfoldPolicy) :
    Environment :=
  let p := (getUnfoldPolicy? env declName (sync := true)).getD { declName }
  unfoldPolicyExt.addEntry env (f p)

private def activePrefix : Name := `_unfolding

def Options.isUnfoldingActive (opts : Options) (declName : Name) : Bool :=
  opts.contains (activePrefix ++ declName)

def Options.getActiveUnfoldings (opts : Options) : Array Name := Id.run do
  let mut ns := #[]
  for (k, _) in opts do
    if activePrefix.isPrefixOf k then
      ns := ns.push (k.replacePrefix activePrefix .anonymous)
  return ns

/--
Closes `ns` upwards: activating a `controlled` declaration also activates the names its value was
checked under, and activating an abbreviation means activating the names it abbreviates.
-/
partial def closeUnfoldings (env : Environment) (ns : Array Name) : Array Name :=
  (go ns.toList {}).toArray
where
  go : List Name → NameSet → NameSet
    | [], s => s
    | n :: ns, s =>
      if s.contains n then go ns s
      else
        let s := s.insert n
        match getUnfoldPolicy? env n with
        | some p => go (p.requires.toList ++ ns) s
        | none   => go ns s

/-- Adds `ns` to the active set; callers should close `ns` with `closeUnfoldings` first. -/
def Options.activateUnfoldings (opts : Options) (ns : Array Name) : Options :=
  ns.foldl (fun opts n => opts.setBool (activePrefix ++ n) true) opts

/-- Runs `x` with `ns`, closed under `closeUnfoldings`, added to the active set. -/
def withUnfoldings [Monad m] [MonadEnv m] [MonadWithOptions m] (ns : Array Name) (x : m α) : m α := do
  let ns := closeUnfoldings (← getEnv) ns
  withOptions (·.activateUnfoldings ns) x

/-- Runs `x` with an empty active set. -/
def withoutUnfoldings [MonadWithOptions m] (x : m α) : m α :=
  withOptions (fun opts => opts.getActiveUnfoldings.foldl (fun opts n => opts.erase (activePrefix ++ n)) opts) x

/--
Whether the policy of `declName` allows delta-unfolding it under the active set of `opts`. See
`getUnfoldPolicy?` for `sync`.
-/
def canUnfoldUnderPolicy (env : Environment) (opts : Options) (declName : Name) (sync := false) :
    Bool :=
  match getUnfoldPolicy? env declName sync with
  | none   => true
  | some p =>
    if p.controlled then opts.isUnfoldingActive declName
    else p.requires.all opts.isUnfoldingActive

/-- Whether the rewrite rule `declName` may fire under the active set of `opts`. -/
def isRewriteRuleActive (env : Environment) (opts : Options) (declName : Name) : Bool :=
  match getUnfoldPolicy? env declName with
  | some { guardedRule := true, .. } => opts.isUnfoldingActive declName
  | _ => true

/--
Records that the values of the declarations in `decl` are checked under the current active set, if
it is not empty. Called by `addDecl` before the declaration is sent to the kernel.
-/
def recordUnfoldScope (decl : Declaration) : CoreM Unit := do
  let active := (← getOptions).getActiveUnfoldings
  if active.isEmpty then return
  match decl with
  | .defnDecl .. | .thmDecl .. | .opaqueDecl .. | .mutualDefnDecl .. =>
    for n in decl.getNames do
      modifyEnv (unfoldPolicyExt.addEntry · { declName := n, requires := active })
  | _ => pure ()

@[export lean_kernel_has_unfold_policies]
private def kernelHasUnfoldPolicies (env : Kernel.Environment) : Bool :=
  !Std.TreeMap.isEmpty (env.getPersistentExtState unfoldPolicyExt).2

/-- `0`: no policy, `1`: abbreviation, `2`: controlled, plus `4` for guarded rewrite rules. -/
@[export lean_kernel_unfold_policy_kind]
private def kernelUnfoldPolicyKind (env : Kernel.Environment) (declName : Name) : UInt8 :=
  match (env.getPersistentExtState unfoldPolicyExt).2.find? declName with
  | none   => 0
  | some p => (if p.controlled then 2 else 1) ||| (if p.guardedRule then 4 else 0)

@[export lean_kernel_unfold_policy_requires]
private def kernelUnfoldPolicyRequires (env : Kernel.Environment) (declName : Name) : List Name :=
  match (env.getPersistentExtState unfoldPolicyExt).2.find? declName with
  | none   => []
  | some p => p.requires.toList

end Lean
