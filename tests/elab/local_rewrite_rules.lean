import Lean

set_option pp.mvars false

/-!
Tests for local rewrite rules: parameters `h : LocalRewrite (∀ xs, lhs = rhs)` that turn `lhs ↦ rhs`
into a reduction rule while checking the declaration they belong to, following Leray and
Winterhalter's Local Rewriting Type Theory and Agda's `@rewrite` module parameters.
-/

/-! ## Parametric addition, as in Agda's documentation -/

section ParametricAddition
variable (N : Type) (zero : N) (succ : N → N)
  (rec : (P : N → Type) → P zero → ((n : N) → P n → P (succ n)) → (n : N) → P n)
  {rec_zero : LocalRewrite (∀ P z s, rec P z s zero = z)}
  {rec_succ : LocalRewrite (∀ P z s n, rec P z s (succ n) = s n (rec P z s n))}
  (ind : (P : N → Prop) → P zero → ((n : N) → P n → P (succ n)) → (n : N) → P n)

def add (n m : N) : N := rec (fun _ => N) m (fun _ => succ) n

local notation:65 a:65 " +' " b:66 => add N zero succ rec a b

theorem zero_add (n : N) : zero +' n = n := rfl
theorem succ_add (n m : N) : succ n +' m = succ (n +' m) := rfl

-- Without the rules, this proof would need to rewrite with `rec_zero` and `rec_succ`.
include ind in
theorem add_assoc (n m l : N) : n +' m +' l = n +' (m +' l) :=
  ind (fun k => k +' m +' l = k +' (m +' l)) rfl (fun _ h => congrArg succ h) n

-- Tactics see the rules too, and `simp` and `rw` prove the rules of the lemmas they instantiate.
example (n : N) : succ zero +' n = succ n := by rfl
example (n : N) : succ (succ zero) +' n = succ (succ n) := by simp only [succ_add, zero_add]
example (n : N) : succ (succ zero) +' n = succ (succ n) := by rw [succ_add, succ_add, zero_add]
example (n : N) : zero +' (zero +' n) = n := by simp [zero_add]

-- Recursive definitions inside the interface.
def double : N → Nat → N
  | n, 0 => n
  | n, k + 1 => double (n +' n) k

theorem double_zero (k : Nat) : double N zero succ rec zero k = zero := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

def addIter (n : N) (k : Nat) : N :=
  if h : k = 0 then n else addIter (succ zero +' n) (k - 1)
termination_by k
decreasing_by omega

theorem addIter_one (n : N) : addIter N zero succ rec n 1 = succ n := by
  rw [addIter, addIter]; rfl

end ParametricAddition

/-- info: add (N : Type) (zero : N) (succ : N → N) (rec : (P : N → Type) → P zero → ((n : N) → P n → P (succ n)) → (n : N) → P n)
  {rec_zero : LocalRewrite (∀ (P : N → Type) (z : P zero) (s : (n : N) → P n → P (succ n)), rec P z s zero = z)}
  {rec_succ :
    LocalRewrite
      (∀ (P : N → Type) (z : P zero) (s : (n : N) → P n → P (succ n)) (n : N), rec P z s (succ n) = s n (rec P z s n))}
  (n m : N) : N -/
#guard_msgs in
#check add

/-! ### Instantiating the interface -/

-- `Nat.rec` satisfies the rules definitionally, so the `LocalRewrite` arguments are filled in.
def natAdd := add Nat 0 Nat.succ (fun P z s n => Nat.rec (motive := P) z s n)

example : natAdd 2 3 = 5 := rfl
example : natAdd 2 3 = 5 := by decide

theorem natAdd_assoc (a b c : Nat) : natAdd (natAdd a b) c = natAdd a (natAdd b c) :=
  add_assoc Nat 0 Nat.succ (fun P z s n => Nat.rec (motive := P) z s n)
    (fun P z s n => Nat.rec (motive := P) z s n) a b c

/-- info: 'natAdd_assoc' does not depend on any axioms -/
#guard_msgs in
#print axioms natAdd_assoc

-- A different encoding of the natural numbers.
def unitListRec (P : List Unit → Type) (z : P []) (s : (n : List Unit) → P n → P (() :: n)) :
    (n : List Unit) → P n
  | [] => z
  | () :: n => s n (unitListRec P z s n)

def unitListAdd := add (List Unit) [] (() :: ·) unitListRec

example : unitListAdd [(), ()] [()] = [(), (), ()] := rfl

/-! ### Instances that do not compute -/

axiom badRec : (P : Nat → Type) → P 0 → ((n : Nat) → P n → P (n + 1)) → (n : Nat) → P n
axiom badRec_zero : ∀ P z s, badRec P z s 0 = z
axiom badRec_succ : ∀ P z s n, badRec P z s (n + 1) = s n (badRec P z s n)

/--
error: could not synthesize default value for parameter 'rec_zero' using tactics
---
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  badRec P z s 0 = z
---
error: could not synthesize default value for parameter 'rec_succ' using tactics
---
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  badRec P z s n.succ = s n (badRec P z s n)
-/
#guard_msgs in
noncomputable example := add Nat 0 Nat.succ badRec

-- A propositional proof is accepted by the elaborator, but the kernel checks the rules definitionally.
/--
error: (kernel) invalid application
  add Nat 0 Nat.succ badRec
a local rewrite rule argument does not hold definitionally: the left-hand side
  badRec P z s 0
is not definitionally equal to the right-hand side
  z
-/
#guard_msgs in
noncomputable example := add Nat 0 Nat.succ badRec (rec_zero := badRec_zero) (rec_succ := badRec_succ)

/-! ### Declarations with an interface must be applied to it -/

-- The elaborator allows partial applications, e.g. for `rw`, but the kernel rejects them.

/--
error: (kernel) invalid occurrence of 'add', it has local rewrite rule parameters and must be applied to at least 6 arguments
-/
#guard_msgs in
example := @add

/--
error: (kernel) invalid occurrence of 'add', it has local rewrite rule parameters and must be applied to at least 6 arguments
-/
#guard_msgs in
example := @add Nat 0 Nat.succ (fun P z s n => Nat.rec (motive := P) z s n)

/-! ## Rules on non-function parameters and declaration parameters -/

def toFinOne (n : Nat) {h : LocalRewrite (n = 0)} (i : Fin (n + 1)) : Fin 1 := i

example : toFinOne 0 (3 : Fin 1) = 0 := rfl

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  1 = 0
-/
#guard_msgs in
example := toFinOne 1 (3 : Fin 2)

/-! ## Non-linear patterns and parameter-headed subpatterns -/

theorem idem (f : Nat → Nat → Nat) (g : Nat → Nat)
    (h₁ : LocalRewrite (∀ x, f x x = x)) (h₂ : LocalRewrite (∀ x, g (g x) = g x)) (n : Nat) :
    f (g (g n)) (g n) = g n := rfl

/-! ## Local rewrite rules are only active for parameters -/

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  f 0 = 1
-/
#guard_msgs in
example (f : Nat → Nat) : LocalRewrite (f 0 = 1) → f 0 = 1 := fun _ => rfl

/--
error: Tactic `rfl` failed: The left-hand side
  f 0
is not definitionally equal to the right-hand side
  1

f : Nat → Nat
h : LocalRewrite (f 0 = 1)
⊢ f 0 = 1
-/
#guard_msgs in
example (f : Nat → Nat) : LocalRewrite (f 0 = 1) → f 0 = 1 := by
  intro h
  rfl

/-! ## Invalid rules -/

/--
error: invalid local rewrite rule `h`: the left-hand side must be an application of an earlier parameter
  n + 0
-/
#guard_msgs in
example (h : LocalRewrite (∀ n : Nat, n + 0 = n)) : True := trivial

/--
error: invalid local rewrite rule `h`: variable `m` does not occur in a pattern position of the left-hand side
  f n
-/
#guard_msgs in
example (f : Nat → Nat) (h : LocalRewrite (∀ n m : Nat, f n = m)) : True := trivial

/--
error: invalid local rewrite rule `h`: the conclusion must be an equality
  True
-/
#guard_msgs in
example (h : LocalRewrite True) : True := trivial

/--
error: invalid local rewrite rule `h`: the conclusion must be an equality
  True
-/
#guard_msgs in
variable (h : LocalRewrite True)

/-! ## Strictified renamings (Leray and Winterhalter, Section 7.1) -/

section Renaming
variable (Ren : Type) (renVar : Ren → Nat → Nat) (upRen : Ren → Ren) (shiftRen : Ren)
  (compRen : Ren → Ren → Ren) (idRen : Ren)
  {r₁ : LocalRewrite (∀ σ, renVar (upRen σ) 0 = 0)}
  {r₂ : LocalRewrite (∀ σ n, renVar (upRen σ) (Nat.succ n) = Nat.succ (renVar σ n))}
  {r₃ : LocalRewrite (∀ n, renVar shiftRen n = Nat.succ n)}
  {r₄ : LocalRewrite (∀ σ τ n, renVar (compRen σ τ) n = renVar σ (renVar τ n))}
  {r₅ : LocalRewrite (∀ n, renVar idRen n = n)}
  {r₆ : LocalRewrite (∀ σ, compRen idRen σ = σ)}
  {r₇ : LocalRewrite (∀ σ, compRen σ idRen = σ)}
  {r₈ : LocalRewrite (∀ σ τ ρ, compRen (compRen σ τ) ρ = compRen σ (compRen τ ρ))}

theorem upRen_shift (σ : Ren) (n : Nat) :
    renVar (compRen (upRen σ) (compRen shiftRen idRen)) n = Nat.succ (renVar σ n) := rfl

theorem comp_assoc_id (σ τ ρ : Ren) :
    compRen (compRen idRen (compRen σ τ)) ρ = compRen σ (compRen τ (compRen ρ idRen)) := rfl

end Renaming

def funUpRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

-- Functions satisfy all the rules, including the unit and associativity laws, definitionally.
example (σ : Nat → Nat) (n : Nat) : funUpRen σ (Nat.succ n) = Nat.succ (σ n) :=
  upRen_shift (Nat → Nat) id funUpRen Nat.succ (fun ρ ρ' n => ρ (ρ' n)) id σ n

/-! ## Nested proofs are abstracted together with the rules they need -/

def castFin (n : Nat) {h : LocalRewrite (n = 0)} (i : Fin (n + 1)) : Fin 1 :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_refl _)⟩

example : castFin 0 (0 : Fin 1) = 0 := rfl

/-! ## The kernel enforces the interface on its own -/

section
open Lean Meta

-- `toFinOne` itself, without its argument.
/--
error: (kernel) invalid occurrence of 'toFinOne', it has local rewrite rule parameters and must be applied to at least 2 arguments
-/
#guard_msgs in
run_meta addDecl <| .defnDecl {
  name := `bareToFinOne, levelParams := [], hints := .opaque, safety := .safe
  type := (← inferType (mkConst ``toFinOne))
  value := mkConst ``toFinOne }

-- A lambda-bound `LocalRewrite` hypothesis is not a rule: `fun h => toFinOne 1 h` is rejected.
/--
error: (kernel) invalid application
  toFinOne 1
a local rewrite rule argument does not hold definitionally: the left-hand side
  1
is not definitionally equal to the right-hand side
  0
-/
#guard_msgs in
run_meta do
  let n := mkNatLit 1
  let hType := mkApp (mkConst ``LocalRewrite) (← mkEq n (mkNatLit 0))
  let value := mkLambda `h .default hType (mkApp2 (mkConst ``toFinOne) n (.bvar 0))
  addDecl <| .defnDecl {
    name := `lambdaToFinOne, levelParams := [], hints := .opaque, safety := .safe
    type := (← inferType value), value }

-- The kernel uses the rule of a parameter while checking the declaration it belongs to.
run_meta do
  let nat := mkConst ``Nat
  -- `fun (n : Nat) (h : LocalRewrite (n = 0)) (i : Fin (n + 1)) => (i : Fin 1)`
  withLocalDeclD `n nat fun n => do
  withLocalDeclD `h (mkApp (mkConst ``LocalRewrite) (← mkEq n (mkNatLit 0))) fun h => do
  let finOne := mkApp (mkConst ``Fin) (mkNatLit 1)
  withLocalDeclD `i (mkApp (mkConst ``Fin) (← mkAdd n (mkNatLit 1))) fun i => do
  addDecl <| .defnDecl {
    name := `kernelToFinOne, levelParams := [], hints := .opaque, safety := .safe
    type := (← mkForallFVars #[n, h, i] finOne)
    value := (← mkLambdaFVars #[n, h, i] i) }

-- An applied lambda with `LocalRewrite` binders is checked like a declaration with an interface:
-- `(fun (n : Nat) (h : LocalRewrite (n = 0)) (i : Fin (n + 1)) => (id i : Fin 1)) m p`.
def mkFinRedex (m p : Expr) : MetaM Expr := do
  let nat := mkConst ``Nat
  let finOne := mkApp (mkConst ``Fin) (mkNatLit 1)
  let fn ← withLocalDeclD `n nat fun n => do
    withLocalDeclD `h (mkApp (mkConst ``LocalRewrite) (← mkEq n (mkNatLit 0))) fun h => do
    withLocalDeclD `i (mkApp (mkConst ``Fin) (← mkAdd n (mkNatLit 1))) fun i => do
    mkLambdaFVars #[n, h, i] (mkApp2 (mkConst ``id [1]) finOne i)
  return mkApp2 fn m p

run_meta do
  let value ← mkFinRedex (mkNatLit 0) (← mkEqRefl (mkNatLit 0))
  addDecl <| .defnDecl {
    name := `finRedex, levelParams := [], hints := .opaque, safety := .safe
    type := (← mkArrow (mkApp (mkConst ``Fin) (← mkAdd (mkNatLit 0) (mkNatLit 1))) (mkApp (mkConst ``Fin) (mkNatLit 1)))
    value }

/--
error: (kernel) invalid application
  (fun n h i => id i) 1 p
a local rewrite rule argument does not hold definitionally: the left-hand side
  1
is not definitionally equal to the right-hand side
  0
-/
#guard_msgs in
run_meta do
  withLocalDeclD `p (← mkEq (mkNatLit 1) (mkNatLit 0)) fun p => do
  let value ← mkLambdaFVars #[p] (← mkFinRedex (mkNatLit 1) p)
  addDecl <| .defnDecl {
    name := `finRedex', levelParams := [], hints := .opaque, safety := .safe
    type := (← inferType value), value }

-- The same declaration without the rule is rejected.
/--
error: (kernel) declaration type mismatch, 'kernelToFinOne'' has type
  (n : Nat) → n = 0 → Fin (n + 1) → Fin (n + 1)
but it is expected to have type
  (n : Nat) → n = 0 → Fin (n + 1) → Fin 1
-/
#guard_msgs in
run_meta do
  let nat := mkConst ``Nat
  withLocalDeclD `n nat fun n => do
  withLocalDeclD `h (← mkEq n (mkNatLit 0)) fun h => do
  let finOne := mkApp (mkConst ``Fin) (mkNatLit 1)
  withLocalDeclD `i (mkApp (mkConst ``Fin) (← mkAdd n (mkNatLit 1))) fun i => do
  addDecl <| .defnDecl {
    name := `kernelToFinOne', levelParams := [], hints := .opaque, safety := .safe
    type := (← mkForallFVars #[n, h, i] finOne)
    value := (← mkLambdaFVars #[n, h, i] i) }
end
