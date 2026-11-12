/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

prelude
public import Lean.EnvExtension

public section

/-!
# The environment extension storing `@[rewrite_rule]` rules

See `Lean.RewriteRules` for the feature. The extension lives in this low-level module so that axiom
collection (`Lean.Util.CollectAxioms`) can account for the declarations justifying the rules.
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
    -- Type class resolution may read the rules while recording dependencies.
    logWrites     := true
  }

/-- Rewrite rules whose left-hand side is headed by `head`, in the order in which they were declared. -/
def getRewriteRules (env : Environment) (head : Name) : Array RewriteRule :=
  -- Rules are only added on the main branch, so the local state is up to date and does not block.
  (rewriteRuleExt.getState env (asyncMode := .local)).find? head |>.getD #[]

/-- Whether any rewrite rules have been declared. -/
def hasRewriteRules (env : Environment) : Bool :=
  !Std.TreeMap.isEmpty (rewriteRuleExt.getState env (asyncMode := .local))

@[export lean_kernel_has_rewrite_rules]
private def kernelHasRewriteRules (env : Kernel.Environment) : Bool :=
  !Std.TreeMap.isEmpty (env.getPersistentExtState rewriteRuleExt).2

/-- Names of the declarations justifying the rewrite rules headed by `head`, in the order in which
they are tried: later rules first. -/
@[export lean_kernel_get_rewrite_rules]
private def kernelGetRewriteRules (env : Kernel.Environment) (head : Name) : List Name :=
  match (env.getPersistentExtState rewriteRuleExt).2.find? head with
  | some rs => rs.toList.reverse.map (·.declName)
  | none    => []

/-- Heads of all rewrite rules. -/
@[export lean_kernel_get_rewrite_rule_heads]
private def kernelGetRewriteRuleHeads (env : Kernel.Environment) : List Name :=
  (Std.TreeMap.toList (env.getPersistentExtState rewriteRuleExt).2).map (·.1)

/-- All rewrite rules, keyed by the head of their left-hand side. -/
def getAllRewriteRules (env : Environment) : RewriteRules :=
  rewriteRuleExt.getState env (asyncMode := .local)

end Lean
