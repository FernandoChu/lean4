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
* an application `c q₁ ... qₘ` of a constant to patterns, matched against the target after
  rewriting and unfolding it one step at a time until `c` is at its head (and further, if the
  arguments do not match), or
* any other term, matched up to definitional equality once the variables it mentions are bound.

Implicit and instance arguments of constant applications are determined by the explicit arguments,
but only up to definitional equality: an index `f ≫ g` in the type of an argument may be reached as
`𝟙 x` in the target, and the same instance can be reached along different paths. So the implicit
arguments that are variables are bound first, then the explicit arguments are matched, and the other
implicit arguments are checked up to definitional equality once their variables are bound, or
matched structurally, falling back to definitional equality, if not. A variable that occurs only in
such an argument is left unbound when that argument does not match structurally, and then the rule
does not fire.

Every variable in `xs` and every universe parameter of `h` must occur in a pattern position of
the left-hand side, i.e. one of the first two forms.

Rules whose head is a projection function, such as `Hom.app`, also fire on the corresponding
primitive projection `η.1`. When several rules apply to a term, the one declared last is used: later
rules are usually more specific, and a general rule such as associativity could otherwise fire first
after unfolding a subterm with another rule. When definitional equality compares two applications of
the same rule head, it compares their arguments before rewriting either side, as lazy delta
reduction does for definitions.

This is an experimental feature. Neither confluence nor termination of the resulting rewrite system
is checked, so rules can make type checking loop or break subject reduction. A rule justified by an
axiom is only as trustworthy as that axiom.

The kernel does not trust the stored rule: it only reads the names of the tagged declarations and
re-derives each rule from the declaration's type (see `type_checker::reduce_rewrite_rule`).

# Local rewrite rules

A parameter `h : LocalRewrite (∀ xs, lhs = rhs)` of a declaration (see `LocalRewrite`) is a rewrite
rule local to that declaration, following Leray and Winterhalter's Local Rewriting Type Theory
("Encode the Cake and Eat It Too", POPL 2026). The left-hand side must be headed by an earlier
parameter rather than by a constant, and the patterns may also use earlier parameters as rigid heads.
The elaborator activates these rules with `Meta.withLocalRewriteRules`. The kernel activates them
while checking the declaration (`type_checker::check_interface_type`) and checks at every use of the
declaration that they hold definitionally (`type_checker::infer_interface_app`).
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

/-- Records the variables and universe parameters bound by the pattern positions of `p`. Other
subterms are matched up to definitional equality and bind nothing. -/
private partial def checkPattern (p : Expr) : StateM PatternInfo Unit := do
  if !p.hasLooseBVars then return
  match p.consumeMData with
  | .bvar i => modify fun s => { s with vars := s.vars.set! i true }
  | p@(.app ..) =>
    match p.getAppFn with
    | .const _ us => modify fun s => { s with lvls := collectLevelParams us s.lvls }
    | .fvar _     => pure ()
    | _           => return
    p.getAppArgs.forM checkPattern
  | _ => return

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
  let ((), s) := (lhsArgs.forM checkPattern).run init
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
  -- A rule changes how its head reduces, so results recorded about the head are invalidated.
  modifyEnv (rewriteRuleExt.addEntry (log := .decl rule.head) · rule)

/-- Returns `p` if `type` is `LocalRewrite p`. -/
def Expr.localRewrite? (type : Expr) : Option Expr :=
  let type := type.consumeMData
  if type.isAppOfArity ``LocalRewrite 1 then some type.appArg! else none

/--
The number of leading binders of a declaration type `type` up to and including the last one of the
form `LocalRewrite _`, i.e. the number of arguments every use of the declaration must be applied to.
This mirrors the kernel's `interface_arity`.
-/
def interfaceArity (type : Expr) : Nat :=
  go type 0 0
where
  go : Expr → Nat → Nat → Nat
    | .forallE _ d b _, i, k => go b (i + 1) (if d.localRewrite?.isSome then i + 1 else k)
    | .mdata _ e,       i, k => go e i k
    | _,                _, k => k

/-- The interface arity (see `interfaceArity`) of the constant `c`. -/
def getInterfaceArity (c : Name) : CoreM Nat := do
  let some info := (← getEnv).findAsync? c | return 0
  unless info.kind matches .defn | .thm | .opaque | .axiom do return 0
  return interfaceArity info.sig.get.type

namespace Meta

/--
Decodes the local rewrite rule of a hypothesis `h : LocalRewrite (∀ xs, lhs = rhs)`, or returns
`none` if the type of `h` does not have the form `LocalRewrite _`. See `LocalRewrite`.
-/
def mkLocalRewriteRule? (h : Expr) : MetaM (Option LocalRewriteRule) := do
  let fvarId := h.fvarId!
  let some eqn := (← instantiateMVars (← fvarId.getType)).localRewrite? | return none
  let (xs, body) := stripForalls eqn
  let numVars := xs.size
  let throwAt {α} (msg : MessageData) (e : Expr) : MetaM α :=
    forallBoundedTelescope eqn (some numVars) fun fvars _ =>
      throwError "invalid local rewrite rule `{h}`: {msg}{indentExpr (e.instantiateRev fvars)}"
  let some (_, lhs, rhs) := body.consumeMData.eq? |
    throwAt "the conclusion must be an equality" body
  let lhs := lhs.consumeMData
  let .fvar head := lhs.getAppFn |
    throwAt "the left-hand side must be an application of an earlier parameter" lhs
  if (← head.getDecl).isLet then
    throwAt m!"the head `{mkFVar head}` of the left-hand side must not be a let-variable" lhs
  let ((), s) := (lhs.getAppArgs.forM checkPattern).run { vars := .replicate numVars false }
  for i in [:numVars] do
    unless s.vars[i]! do
      throwAt m!"variable `{xs[numVars - 1 - i]!}` does not occur in a pattern position of the \
        left-hand side" lhs
  return some { fvarId, head, numVars, lhs, rhs }

/--
Runs `k` with the local rewrite rules of the hypotheses among `fvars` whose type has the form
`LocalRewrite _` active, see `LocalRewrite`. This should only be used for the parameters of the
declaration being elaborated, as the kernel only uses the rules of these parameters.
-/
def withLocalRewriteRules [MonadControlT MetaM n] [Monad n] (fvars : Array Expr) (k : n α) : n α :=
  mapMetaM (fun k => do
    let rules ← fvars.filterMapM mkLocalRewriteRule?
    if rules.isEmpty then
      k
    else
      -- Reductions and failed unifications may have been cached before the rules were active.
      withFreshCache <| withReader (fun ctx => { ctx with localRewriteRules := ctx.localRewriteRules ++ rules }) k) k

/--
Runs `k` on the body of the declaration value `value` under its first `interfaceArity type` binders,
with the local rewrite rules of these binders active, and abstracts the binders again. This is for
post-processing a declaration value outside of the context in which it was elaborated.
-/
def mapInterfaceBody (type value : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  let arity := interfaceArity type
  if arity == 0 then
    k value
  else
    lambdaBoundedTelescope value arity fun xs body =>
      withLocalRewriteRules xs do mkLambdaFVars xs (← k body)

/--
Proves `LocalRewrite (∀ xs, lhs = rhs)` by reflexivity if `lhs` and `rhs` are definitionally equal,
which is what the kernel checks for an argument of this type of a declaration with an interface.
-/
def mkLocalRewriteProof? (type : Expr) : MetaM (Option Expr) := do
  let some eqn := (← instantiateMVars type).localRewrite? | return none
  forallTelescope eqn fun xs body => do
    let body := body.consumeMData
    let some (α, lhs, rhs) := body.eq? | return none
    unless (← withTransparency .all <| isDefEq lhs rhs) do return none
    return some (← mkLambdaFVars xs (mkApp2 (mkConst ``Eq.refl body.getAppFn.constLevels!) α lhs))

/-- The local rewrite rules whose left-hand side is headed by `head`. -/
def getLocalRewriteRules (head : FVarId) : MetaM (Array LocalRewriteRule) := do
  let rules := (← read).localRewriteRules
  if rules.isEmpty then return #[]
  let lctx ← getLCtx
  return rules.filter fun rule => rule.head == head && lctx.contains rule.fvarId

end Meta

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

end Lean
