/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.MonadEnv
public import Lean.RewriteRuleExt

namespace Lean

namespace CollectAxioms

structure State where
  /-- Cache mapping constants to their (sorted) axiom dependencies. -/
  seen   : NameMap (Array Name) := {}
  /-- Axioms accumulated for the current constant being processed. -/
  axioms : NameSet := {}

abbrev M := ReaderT Environment $ StateM State

def runM (env : Environment) (x : M α) : α :=
  x.run env |>.run' {}

def insertArray (s : NameSet) (axs : Array Name) : NameSet :=
  axs.foldl (init := s) fun acc ax => acc.insert ax

/--
Collect axioms reachable from constant `c`, using `extFind?` to look up pre-computed axioms
for imported declarations. Results are cached in `State.seen`.

When processing a constant not found in `extFind?` or the cache, the function temporarily
clears the axiom accumulator, recurses into the constant's dependencies, caches the result
in `seen`, and merges the collected axioms back.
-/
partial def collect
    (extFind? : Environment → Name → Option (Array Name))
    (c : Name) : M Unit := do
  let env ← read
  -- Check extension for pre-computed axioms (imported declarations)
  if let some axs := extFind? env c then
    modify fun s => { s with axioms := insertArray s.axioms axs, seen := s.seen.insert c axs }
    return
  -- Check local cache
  let s ← get
  if let some axs := s.seen.find? c then
    modify fun s => { s with axioms := insertArray s.axioms axs }
    return
  -- Recurse: temporarily clear axioms to isolate this constant's contribution.
  -- Insert sentinel to prevent infinite recursion (e.g., inductives ↔ constructors).
  let savedAxioms := s.axioms
  modify fun s => { s with axioms := {}, seen := s.seen.insert c #[] }
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM (collect extFind?)
  -- Take constants from the kernel env, which may differ from the elab env for (async) errors.
  match env.checked.get.find? c with
  | some (.axiomInfo v)  =>
      modify fun s => { s with axioms := s.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => collectExpr v.type
  | some (.recInfo v)    => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM (collect extFind?)
  | none                 => pure ()
  -- Cache result (sorted for canonical order) and merge back into saved axioms
  let collected := (← get).axioms
  let result := collected.toArray.qsort Name.lt
  modify fun s => { s with
    seen   := s.seen.insert c result
    axioms := insertArray savedAxioms result
  }

/-- Records the constants occurring in `e`, and the structures whose primitive projections occur in
`e`, in the second and third components of the state. -/
unsafe def reachUnsafe (e : Expr) : StateM (PtrSet Expr × NameSet × NameSet) Unit := do
  if (← get).1.contains e then return
  modify fun (v, cs, ss) => (v.insert e, cs, ss)
  match e with
  | .const n _       => modify fun (v, cs, ss) => (v, cs.insert n, ss)
  | .proj sn _ b     => modify (fun (v, cs, ss) => (v, cs, ss.insert sn)) *> reachUnsafe b
  -- The kernel expands string literals into applications of these constants.
  | .lit (.strVal _) => modify fun (v, cs, ss) => (v, (cs.insert `Char.ofNat).insert `String.ofList, ss)
  | .app f a         => reachUnsafe f *> reachUnsafe a
  | .lam _ d b _     => reachUnsafe d *> reachUnsafe b
  | .forallE _ d b _ => reachUnsafe d *> reachUnsafe b
  | .letE _ t v b _  => reachUnsafe t *> reachUnsafe v *> reachUnsafe b
  | .mdata _ b       => reachUnsafe b
  | _                => pure ()

unsafe def reachExprsUnsafe (es : List Expr) : NameSet × NameSet :=
  let (_, cs, ss) := (es.forM reachUnsafe).run (mkPtrSet, {}, {}) |>.2
  (cs, ss)

/-- The constants and the structures of the primitive projections occurring in `es`. -/
@[implemented_by reachExprsUnsafe]
opaque reachExprs (es : List Expr) : NameSet × NameSet

/-- The constants the kernel may reach from the declaration `info` by reduction. -/
def reachConstantInfo (info : ConstantInfo) : NameSet × NameSet :=
  reachExprs <| match info with
    | .defnInfo v    => [v.type, v.value]
    | .thmInfo v     => [v.type, v.value]
    | .opaqueInfo v  => [v.type, v.value]
    | .recInfo v     => v.type :: v.rules.map (·.rhs)
    | .inductInfo v  => v.type :: v.ctors.map (mkConst ·)
    | info           => [info.type]

/--
The declarations justifying the `@[rewrite_rule]`s that the kernel may have applied while checking
`c` or a declaration `c` depends on. A rule can only fire on a term headed by its head constant, or
by a primitive projection if the head is a projection function, so it is enough to follow the
constants and projections reachable from `c` and from the rules found along the way.
-/
partial def reachableRewriteRules (env : Environment) (c : Name) : Array Name :=
  let rules := getAllRewriteRules env
  if rules.isEmpty then #[] else
  let rec go (todo : List Name) (seen structs : NameSet) (result : Array Name) : Array Name :=
    match todo with
    | [] => result
    | n :: todo =>
      let ruleDecls := (rules.find? n |>.getD #[]).map (·.declName)
      let result := result ++ ruleDecls
      let (cs, ss) := match env.checked.get.find? n with
        | some info => reachConstantInfo info
        | none      => ({}, {})
      let newStructs := ss.toList.filter (!structs.contains ·)
      let structs := newStructs.foldl (·.insert ·) structs
      let projHeads := if newStructs.isEmpty then [] else
        rules.toList.filterMap fun (head, _) =>
          if newStructs.contains head.getPrefix then some head else none
      let (todo, seen) := (ruleDecls.toList ++ cs.toList ++ projHeads).foldl (init := (todo, seen))
        fun (todo, seen) n => if seen.contains n then (todo, seen) else (n :: todo, seen.insert n)
      go todo seen structs result
  go [c] (({} : NameSet).insert c) {} #[]

/-- Collect axioms for `c` and return its sorted axiom list from the cache. -/
def collectAndGet
    (extFind? : Environment → Name → Option (Array Name))
    (c : Name) : M (Array Name) := do
  collect extFind? c
  let some axs := (← get).seen.find? c | panic! s!"collectAndGet: '{c}' not in seen after collect"
  return axs

end CollectAxioms

/--
Extension state holding imported module entries for efficient lookup of
pre-computed axiom data.

We use `registerPersistentEnvExtension` with manual lookup instead of `MapDeclarationExtension`
because `exportEntriesFnEx` needs to call `collect`, which needs the extension's `find?`, but
`exportEntriesFnEx` is defined inside the `builtin_initialize` that creates the extension and
thus cannot reference it. This state replicates `MapDeclarationExtension.find?`'s per-module
binary search without requiring the extension object.
-/
structure ExportedAxiomsState where
  importedModuleEntries : Array (Array (Name × Array Name)) := #[]

instance : Inhabited ExportedAxiomsState := ⟨{}⟩

/-- Look up pre-computed axioms for an imported declaration. -/
def ExportedAxiomsState.find? (s : ExportedAxiomsState) (env : Environment)
    (c : Name) : Option (Array Name) :=
  match env.getModuleIdxFor? c with
  | some modIdx =>
    if h : modIdx.toNat < s.importedModuleEntries.size then
      match s.importedModuleEntries[modIdx].binSearch (c, #[]) (fun a b => Name.quickLt a.1 b.1) with
      | some entry => some entry.2
      | none       => none
    else none
  | none => none

/--
Environment extension that records axiom dependencies for all declarations in a module.
Entries are computed once by `beforeExportFn` when the olean is serialized, not during
elaboration. During elaboration, `collectAxioms` walks bodies directly. Downstream modules
look up pre-computed entries for imported declarations, so axiom collection never crosses
module boundaries.
-/
builtin_initialize exportedAxiomsExt :
    PersistentEnvExtension (Name × Array Name) (Name × Array Name) ExportedAxiomsState ←
  registerPersistentEnvExtension {
    mkInitial     := pure {}
    addImportedFn := fun importedEntries => pure { importedModuleEntries := importedEntries }
    addEntryFn    := fun s _ => s
    exportEntriesFnEx := fun env s =>
      let exportedEnv := env.setExporting true
      let privateEnv := env.setExporting false
      -- Collect current-module declarations visible in the exported view.
      -- By pre-computing axiom data for every exported declaration, downstream modules can
      -- look up any imported declaration without walking its body, keeping collection
      -- module-local.
      let allNames := env.checked.get.constants.foldStage2
        (fun names name _ =>
          if (exportedEnv.find? name).isSome then names.push name
          else names) #[]
      -- Compute axioms within a shared state (for caching across declarations).
      -- Use `privateEnv` so that `collect` can see all constant bodies.
      let entries := CollectAxioms.runM privateEnv do
        allNames.mapM fun name =>
          return (name, ← CollectAxioms.collectAndGet s.find? name)
      -- Sort by name for binary search at import time.
      let entries := entries.qsort fun a b => Name.quickLt a.1 b.1
      .uniform entries
    asyncMode     := .mainOnly
  }

/--
Collect all axioms transitively used by a constant, including the axioms used by the declarations
justifying the `@[rewrite_rule]`s the kernel may have applied while checking the constant or its
dependencies (see `CollectAxioms.reachableRewriteRules`): terms do not record which rules were used.
-/
public def collectAxioms [Monad m] [MonadEnv m] (constName : Name) : m (Array Name) := do
  let env ← getEnv
  let privateEnv := env.setExporting false
  let s := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rules := CollectAxioms.reachableRewriteRules privateEnv constName
  return CollectAxioms.runM privateEnv do
    let axs ← CollectAxioms.collectAndGet s.find? constName
    if rules.isEmpty then return axs
    rules.forM (CollectAxioms.collect s.find?)
    return (← get).axioms.toArray.qsort Name.lt

end Lean
