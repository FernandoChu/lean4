/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

prelude
public import Lean.ControlledUnfolding
public import Lean.RewriteRules
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Basic
import Lean.Meta.Closure
import Lean.Elab.SyntheticMVars

public section

/-!
# Elaboration of controlled unfolding

The `@[controlled]` attribute, the `unfolding`/`rewriting` command, term and tactic forms, and
`#print unfolding`; see `Lean.ControlledUnfolding`.
-/

namespace Lean.Elab
open Meta

builtin_initialize
  registerBuiltinAttribute {
    name  := `controlled
    descr := "make a definition unfold only within `unfolding` scopes"
    applicationTime := .afterTypeChecking
    add   := fun declName stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == .global do throwAttrMustBeGlobal `controlled kind
      unless (← getConstInfo declName) matches .defnInfo _ do
        throwError "invalid `@[controlled]`, `{declName}` is not a definition"
      modifyEnv (modifyUnfoldPolicy · declName ({ · with controlled := true }))
  }

/--
Resolves the names of an `unfolding` scope, or of a `rewriting` scope if `rules` is set, and closes
them under `closeUnfoldings`.
-/
def resolveUnfoldings (ids : Array Syntax) (rules : Bool) : CoreM (Array Name) := do
  let ns ← ids.mapM fun id => do
    let n ← realizeGlobalConstNoOverloadWithInfo id
    let p? := getUnfoldPolicy? (← getEnv) n
    if rules then
      unless p?.any (·.guardedRule) do
        throwErrorAt id "`{.ofConstName n}` is not a guarded rewrite rule; \
          mark it `@[guarded_rewrite]`"
    else
      match p? with
      | none => throwErrorAt id "`{.ofConstName n}` is not controlled, so it unfolds everywhere; \
          mark it `@[controlled]`"
      | some { guardedRule := true, .. } =>
        throwErrorAt id "`{.ofConstName n}` is a guarded rewrite rule; use `rewriting` instead"
      | some _ => pure ()
    return n
  return closeUnfoldings (← getEnv) ns

private def elabUnfoldingCmd (stx : Syntax) (rules : Bool) : Command.CommandElabM Unit := do
  let ns ← Command.liftCoreM <| resolveUnfoldings stx[1].getSepArgs rules
  Command.modifyScope fun sc => { sc with opts := sc.opts.activateUnfoldings ns }

@[builtin_command_elab Parser.Command.unfolding] def elabUnfolding : Command.CommandElab :=
  (elabUnfoldingCmd · (rules := false))

@[builtin_command_elab Parser.Command.rewriting] def elabRewriting : Command.CommandElab :=
  (elabUnfoldingCmd · (rules := true))

namespace Term

/--
Elaborates `body` against `expectedType?` with `ns` added to the active set, and hoists the result
into an auxiliary declaration that is checked under that active set. Without hoisting, the kernel
would check `body` under the active set of the surrounding declaration.
-/
def elabHoistedUnfolding (ns : Array Name) (body : Syntax) (expectedType? : Option Expr) :
    TermElabM Expr := do
  let expectedType ← tryPostponeIfHasMVars expectedType?
    "`unfolding ... in e` requires a known expected type without metavariables"
  -- the Meta caches are only valid for the active set they were filled under
  let cache := (← getThe Meta.State).cache
  let value ← tryFinally
    (withUnfoldings ns do
      resetCache
      let value ← elabTermEnsuringType body expectedType
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars value)
    (modifyThe Meta.State fun s => { s with cache })
  -- e.g. `Sort ?u` in a type position is resolved now
  let expectedType ← instantiateMVars expectedType
  if value.hasMVar || expectedType.hasMVar then
    throwError "`unfolding ... in e` could not be hoisted into an auxiliary declaration, the \
      elaborated term contains metavariables{indentExpr value}"
  withUnfoldings ns do
    if (← isProp expectedType) then
      mkAuxTheorem expectedType value (kind? := `_unfold)
    else
      let declName ← mkAuxName `_unfold
      let e ← mkAuxDefinition declName expectedType value (logCompileErrors := false)
      setReducibilityStatus declName .reducible
      return e

private def elabUnfoldingTerm (stx : Syntax) (expectedType? : Option Expr) (rules : Bool) :
    TermElabM Expr := do
  let ns ← resolveUnfoldings stx[1].getSepArgs rules
  elabHoistedUnfolding ns stx[3] expectedType?

@[builtin_term_elab Parser.Term.unfolding] def elabUnfolding : TermElab :=
  (elabUnfoldingTerm · · (rules := false))

@[builtin_term_elab Parser.Term.rewriting] def elabRewriting : TermElab :=
  (elabUnfoldingTerm · · (rules := true))

end Term

namespace Tactic

private def evalUnfoldingTac (stx : Syntax) (rules : Bool) : TacticM Unit := do
  let ns ← resolveUnfoldings stx[1].getSepArgs rules
  let mvarId ← getMainGoal
  mvarId.withContext do
    let type ← instantiateMVars (← mvarId.getType)
    let byStx := mkNode ``Parser.Term.byTactic #[mkAtomFrom stx[0] "by", stx[3]]
    let value ← Term.withSynthesize <| Term.elabHoistedUnfolding ns byStx (some type)
    closeMainGoal (if rules then `rewriting else `unfolding) value

@[builtin_tactic Parser.Tactic.unfolding] def evalUnfolding : Tactic :=
  (evalUnfoldingTac · (rules := false))

@[builtin_tactic Parser.Tactic.rewriting] def evalRewriting : Tactic :=
  (evalUnfoldingTac · (rules := true))

end Tactic

@[builtin_command_elab Parser.Command.printUnfolding] def elabPrintUnfolding : Command.CommandElab :=
  fun stx => Command.liftTermElabM do
    let n ← realizeGlobalConstNoOverloadWithInfo stx[2]
    let names (ns : Array Name) : MessageData :=
      .joinSep (ns.toList.map fun n => m!"`{MessageData.ofConstName n}`") ", "
    match getUnfoldPolicy? (← getEnv) n (sync := true) with
    | none => logInfo m!"`{.ofConstName n}` has no unfolding policy, it unfolds everywhere"
    | some p =>
      let requires := p.requires.filter (· != n)
      if p.guardedRule then
        let proved := if requires.isEmpty then m!"" else m!"; it was proved under {names requires}"
        logInfo m!"`{.ofConstName n}` is a guarded rewrite rule, it fires under `rewriting {n}`{proved}"
      else if p.controlled then
        let also := if requires.isEmpty then m!"" else m!", which also unfolds {names requires}"
        logInfo m!"`{.ofConstName n}` is controlled, it unfolds under `unfolding {n}`{also}"
      else
        logInfo m!"`{.ofConstName n}` is an abbreviation, it unfolds where all of these unfold: \
          {names requires}"

end Lean.Elab
