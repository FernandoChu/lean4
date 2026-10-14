/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

prelude
public import Lean.Meta.Basic
public import Lean.Util.Recognizers

public section

/-!
# User-declared rewrite rules

A theorem or axiom `h : ∀ xs, lhs = rhs` tagged with `@[rewrite_rule]` turns `lhs ↦ rhs` into a
reduction rule used by both `Meta.whnfCore` and the kernel's `whnf_core`, in the style of Agda's
`{-# REWRITE #-}` pragma (Cockx, Tabareau, Winterhalter, "The Taming of the Rew", POPL 2021).

The left-hand side must be an application `f p₁ ... pₙ` (`n ≥ 1`) of a constant `f` that is neither
an inductive type nor a constructor. Each pattern `pᵢ` is either
* a variable `x ∈ xs` (repeated occurrences are checked for definitional equality),
* an application `c q₁ ... qₘ` of a constant to patterns, matched against the weak head normal form
  of the target, or
* a term without variables from `xs`, matched up to definitional equality.

Every variable in `xs` and every universe parameter of `h` must be determined by the left-hand side.

`@[guarded_rewrite]` instead declares a rule that only fires within `rewriting` scopes, see
`Lean.ControlledUnfolding`. Only theorems can be guarded rules.

This is an experimental feature. Neither confluence nor termination of the resulting rewrite system
is checked, so rules can make type checking loop or break subject reduction. A rule justified by an
axiom is only as trustworthy as that axiom.

The kernel does not trust the stored rule: it only reads the names of the tagged declarations and
re-derives each rule from the declaration's type (see `type_checker::reduce_rewrite_rule`).
-/

namespace Lean

structure RewriteRule where
  /-- The theorem or axiom `∀ xs, lhs = rhs` justifying the rule. -/
  declName    : Name
  /-- Head constant of the left-hand side. -/
  head        : Name
  levelParams : List Name
  /-- Number of pattern variables, i.e. of leading `∀` binders of the declaration's type. -/
  numVars     : Nat
  /-- Left-hand side `head ps`. Pattern variable `i` is the loose `.bvar i`. -/
  lhs         : Expr
  rhs         : Expr
  deriving Inhabited

abbrev RewriteRules := NameMap (Array RewriteRule)

private def RewriteRules.add (rules : RewriteRules) (r : RewriteRule) : RewriteRules :=
  rules.insert r.head ((rules.find? r.head |>.getD #[]).push r)

builtin_initialize rewriteRuleExt : SimplePersistentEnvExtension RewriteRule RewriteRules ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := RewriteRules.add
    addImportedFn := mkStateFromImportedEntries RewriteRules.add {}
    -- The kernel reads the state from `Environment.checked`, so modifications must reach it.
    asyncMode     := .sync
  }

/-- Rewrite rules whose left-hand side is headed by `head`. -/
def getRewriteRules (env : Environment) (head : Name) : Array RewriteRule :=
  -- Rules are only added on the main branch, so the local state is up to date and does not block.
  (rewriteRuleExt.getState env (asyncMode := .local)).find? head |>.getD #[]

@[export lean_kernel_has_rewrite_rules]
private def kernelHasRewriteRules (env : Kernel.Environment) : Bool :=
  !Std.TreeMap.isEmpty (env.getPersistentExtState rewriteRuleExt).2

/-- Names of the declarations justifying the rewrite rules headed by `head`. -/
@[export lean_kernel_get_rewrite_rules]
private def kernelGetRewriteRules (env : Kernel.Environment) (head : Name) : List Name :=
  match (env.getPersistentExtState rewriteRuleExt).2.find? head with
  | some rs => rs.toList.map (·.declName)
  | none    => []

private partial def stripForalls (e : Expr) (xs : Array Name := #[]) : Array Name × Expr :=
  match e with
  | .forallE x _ b _ => stripForalls b (xs.push x)
  | .mdata _ e       => stripForalls e xs
  | _                => (xs, e)

private structure PatternInfo where
  vars   : Array Bool
  lvls   : NameSet := {}

private def collectLevelParams (us : List Level) (s : NameSet) : NameSet :=
  us.foldl (init := s) fun s u => match u with
    | .param n => s.insert n
    | _        => s

/-- Records the variables and universe parameters bound by pattern `p`, returning the first
unsupported subpattern, if any. -/
private partial def checkPattern (p : Expr) : StateM PatternInfo (Option Expr) := do
  if !p.hasLooseBVars then return none
  match p.consumeMData with
  | .bvar i =>
    modify fun s => { s with vars := s.vars.set! i true }
    return none
  | p@(.app ..) =>
    let .const _ us := p.getAppFn | return some p
    modify fun s => { s with lvls := collectLevelParams us s.lvls }
    for arg in p.getAppArgs do
      if let some bad ← checkPattern arg then return some bad
    return none
  | p => return some p

/-- Validates that `declName : ∀ xs, lhs = rhs` is a well-formed rewrite rule and decodes it. -/
def mkRewriteRule (declName : Name) : MetaM RewriteRule := do
  let env ← getEnv
  let some c := env.findAsync? declName | throwUnknownConstant declName
  unless c.kind matches .thm | .axiom do
    throwError "invalid rewrite rule `{declName}`: must be a theorem or an axiom"
  let info := c.sig.get
  let (xs, body) := stripForalls info.type
  let numVars := xs.size
  -- Displays `e`, which may refer to the pattern variables as loose bound variables.
  let throwAt {α} (msg : MessageData) (e : Expr) : MetaM α :=
    Meta.forallBoundedTelescope info.type (some numVars) fun fvars _ =>
      throwError "invalid rewrite rule `{declName}`: {msg}{indentExpr (e.instantiateRev fvars)}"
  let some (_, lhs, rhs) := body.consumeMData.eq? |
    throwAt "the conclusion must be an equality" body
  let lhs := lhs.consumeMData
  let .const head us := lhs.getAppFn |
    throwAt "the left-hand side must be an application of a constant" lhs
  let lhsArgs := lhs.getAppArgs
  if lhsArgs.isEmpty then
    throwAt m!"the head `{head}` of the left-hand side must be applied to at least one argument" lhs
  match ((env.findAsync? head).map (·.kind) : Option ConstantKind) with
  | some .ctor   => throwAt m!"the head `{head}` is a constructor" lhs
  | some .induct => throwAt m!"the head `{head}` is an inductive type" lhs
  | _ => pure ()
  let init : PatternInfo := { vars := .replicate numVars false, lvls := collectLevelParams us {} }
  let (bad?, s) := (lhsArgs.findSomeM? checkPattern).run init
  if let some bad := bad? then
    throwAt "pattern variables may only occur as arguments of constant applications, \
      but the left-hand side contains the pattern" bad
  for i in [:numVars] do
    unless s.vars[i]! do
      throwAt m!"variable `{xs[numVars - 1 - i]!}` does not occur in a pattern position of the \
        left-hand side" lhs
  for u in info.levelParams do
    unless s.lvls.contains u do
      throwAt m!"universe parameter `{u}` is not bound by the left-hand side" lhs
  return { declName, head, levelParams := info.levelParams, numVars, lhs, rhs }

/-- Adds `declName` as a rewrite rule, see `mkRewriteRule`. -/
def addRewriteRule (declName : Name) : AttrM Unit := do
  let rule ← Meta.MetaM.run' <| mkRewriteRule declName
  modifyEnv (rewriteRuleExt.addEntry · rule)

/--
Adds the theorem `declName` as a rewrite rule that only fires where `declName` is active, see
`Lean.ControlledUnfolding`.
-/
def addGuardedRewriteRule (declName : Name) : AttrM Unit := do
  unless (← getConstInfo declName).isTheorem do
    throwError "invalid guarded rewrite rule `{declName}`: must be a theorem"
  let rule ← Meta.MetaM.run' <| mkRewriteRule declName
  -- the policy must be in place before the rule becomes visible
  modifyEnv (modifyUnfoldPolicy · declName ({ · with guardedRule := true }))
  modifyEnv (rewriteRuleExt.addEntry · rule)

builtin_initialize
  registerBuiltinAttribute {
    name  := `rewrite_rule
    descr := "turn an equation `∀ xs, lhs = rhs` into a definitional reduction rule `lhs ↦ rhs`"
    applicationTime := .afterTypeChecking
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == .global do throwAttrMustBeGlobal `rewrite_rule kind
      addRewriteRule declName
  }

builtin_initialize
  registerBuiltinAttribute {
    name  := `guarded_rewrite
    descr := "turn a theorem `∀ xs, lhs = rhs` into a reduction rule `lhs ↦ rhs` that only fires \
      within `rewriting` scopes"
    applicationTime := .afterTypeChecking
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == .global do throwAttrMustBeGlobal `guarded_rewrite kind
      addGuardedRewriteRule declName
  }

end Lean
