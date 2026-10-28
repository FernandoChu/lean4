import Lean

/-!
Tests for `@[rewrite_rule]`, which turns an equation `∀ xs, lhs = rhs` into a definitional
reduction rule `lhs ↦ rhs` used by both the elaborator and the kernel, in the style of Agda's
`{-# REWRITE #-}` pragma.
-/

/-! ## Addition by recursion on the second argument, with rules for the first -/

def plus : Nat → Nat → Nat
  | n, .zero => n
  | n, .succ m => .succ (plus n m)

theorem plus_zero_left : ∀ n, plus .zero n = n
  | .zero => rfl
  | .succ n => congrArg Nat.succ (plus_zero_left n)

theorem plus_succ_left : ∀ m n, plus (.succ m) n = .succ (plus m n)
  | _, .zero => rfl
  | m, .succ n => congrArg Nat.succ (plus_succ_left m n)

/--
error: Type mismatch
  Eq.refl n
has type
  n = n
but is expected to have type
  plus Nat.zero n = n
-/
#guard_msgs in
example (n : Nat) : plus .zero n = n := Eq.refl n

attribute [rewrite_rule] plus_zero_left plus_succ_left

example (n : Nat) : plus .zero n = n := rfl
example (m n : Nat) : plus (.succ m) n = .succ (plus m n) := rfl
-- `Nat.succ` patterns match numerals.
example (n : Nat) : plus 2 n = n.succ.succ := rfl
-- Rules fire under binders.
example : (fun n => plus .zero n) = id := rfl

/-- info: fun n => n -/
#guard_msgs in
#reduce fun n => plus .zero n

/-! ## The kernel uses the rules on its own -/

section
open Lean

private def mkZeroPlusDecl (name : Name) : Declaration :=
  -- `∀ n, plus Nat.zero n = n`, proved by `fun n => Eq.refl n`
  let nat := mkConst ``Nat
  .thmDecl {
    name, levelParams := []
    type := mkForall `n .default nat <|
      mkApp3 (mkConst ``Eq [1]) nat (mkApp2 (mkConst ``plus) (mkConst ``Nat.zero) (.bvar 0)) (.bvar 0)
    value := mkLambda `n .default nat <| mkApp2 (mkConst ``Eq.refl [1]) nat (.bvar 0)
  }

run_meta addDecl (mkZeroPlusDecl `kernelOnly)

/-- info: 'kernelOnly' does not depend on any axioms -/
#guard_msgs in
#print axioms kernelOnly

-- Without the rule, the kernel would unfold `plus` to `Nat.succ (plus Nat.zero 4)`.
/-- info: 5 -/
#guard_msgs in
run_meta do
  let e := mkApp2 (mkConst ``plus) (mkConst ``Nat.zero) (mkRawNatLit 5)
  logInfo m!"{← ofExceptKernelException (Kernel.whnf (← getEnv) {} e)}"
end

/-! ## A postulated higher inductive type with a computing eliminator -/

axiom Circle : Type
axiom Circle.base : Circle
axiom Circle.loop : Circle.base = Circle.base
axiom Circle.rec {α : Sort u} (b : α) (l : b = b) : Circle → α

@[rewrite_rule]
axiom Circle.rec_base {α : Sort u} (b : α) (l : b = b) : Circle.rec b l Circle.base = b

example (b : Nat) (l : b = b) : Circle.rec b l Circle.base = b := rfl
example (b : Prop) (l : b = b) : Circle.rec b l Circle.base = b := rfl

/-! ## Non-linear patterns -/

axiom diff : Nat → Nat → Nat
@[rewrite_rule] axiom diff_self (n : Nat) : diff n n = 0

example (n : Nat) : diff n n = 0 := rfl
-- Repeated variables are compared up to definitional equality.
example (n : Nat) : diff (plus .zero n) n = 0 := rfl

/--
error: Type mismatch
  Eq.refl 0
has type
  0 = 0
but is expected to have type
  diff n (n + 1) = 0
-/
#guard_msgs in
example (n : Nat) : diff n (n + 1) = 0 := Eq.refl 0

/-! ## Rules apply to over-applied left-hand sides -/

axiom twice : Nat → Nat → Nat
@[rewrite_rule] axiom twice_zero : twice 0 = id

example (n : Nat) : twice 0 n = n := rfl

/-! ## Heads that are projection functions -/

class Unital (α : Type) where
  one : α

axiom act {α : Type} [Unital α] : α → Nat → Nat
@[rewrite_rule] axiom act_one {α : Type} [Unital α] (n : Nat) : act (Unital.one : α) n = n

def ones {α β : Type} [Unital α] [Unital β] : α × β := (Unital.one, Unital.one)

-- Fully unfolding `ones.1` yields a primitive projection out of the instance, so the target must
-- be unfolded step by step until `Unital.one` is at the head.
example {α β : Type} [Unital α] [Unital β] (n : Nat) : act (ones : α × β).1 n = n := rfl

/-! ## Chained rules -/

structure Act where
  obj : Nat → Type
  act {n m : Nat} : obj n → obj m

structure ActHom (P Q : Act) where
  app (n : Nat) : P.obj n → Q.obj n
  app_act {n m : Nat} (x : P.obj n) : app m (P.act x) = Q.act (app n x)

attribute [rewrite_rule] ActHom.app_act

-- The inner rule produces `Q.act _`, a projection function application that full `whnf` would
-- unfold into a primitive projection before the outer rule could match it.
example (P Q R : Act) (η : ActHom P Q) (θ : ActHom Q R) {n m : Nat} (x : P.obj n) :
    θ.app m (η.app m (P.act x)) = R.act (θ.app n (η.app n x)) := rfl

-- A beta-redex in a pattern position must be reduced without unfolding the head it exposes.
example (P Q : Act) (η : ActHom P Q) {n m : Nat} (x : P.obj n) :
    η.app m ((fun y => P.act y) x) = Q.act (η.app n x) := rfl

/-! ## Primitive projections -/

-- Rules on the projection function `ActHom.app` also fire on the primitive projection `η.1`.
-- The kernel meets that form in structure eta, when it compares the types of proof fields.
example (P Q : Act) (η : ActHom P Q) : ActHom.mk (fun n x => η.app n x) η.app_act = η := rfl

open Lean Meta Elab Term in
/-- info: true -/
#guard_msgs in
run_meta do
  let elabClosed (stx : Term) : MetaM Expr := do
    instantiateMVars (← TermElabM.run' (elabTerm stx none))
  let lhs ← elabClosed (← `(fun (P Q : Act) (η : ActHom P Q) (n m : Nat) (x : P.obj n) =>
    η.app m (P.act x)))
  let rhs ← elabClosed (← `(fun (P Q : Act) (η : ActHom P Q) (n m : Nat) (x : P.obj n) =>
    Q.act (η.app n x)))
  let lhs := lhs.replace fun e =>
    if e.isAppOfArity ``ActHom.app 3 then some (.proj ``ActHom 0 e.appArg!) else none
  logInfo m!"{← isDefEq lhs rhs}"

/-! ## Non-pattern subterms -/

-- A subterm of the left-hand side that is not a pattern is matched up to definitional equality,
-- once the variables it mentions are bound by pattern positions.
axiom K : (Nat → Nat) → Nat → Nat
@[rewrite_rule] axiom K_const (n : Nat) : K (fun _ => n) n = n

example (n : Nat) : K (fun _ => n) n = n := rfl
example (n : Nat) : K (fun _ => id n) n = n := rfl

-- Instance arguments are compared up to definitional equality: the rule mentions the parent
-- projection `B.toA inst`, while the term uses the `A` instance directly.
class A (α : Type) where
  a : α
class B (α : Type) extends A α
instance instANat : A Nat := ⟨1⟩
instance instBNat : B Nat := { toA := instANat }

axiom g {α : Type} [B α] : α → α
@[rewrite_rule] axiom g_a {α : Type} [B α] : g (A.a : α) = A.a

example : @g Nat instBNat (@A.a Nat instANat) = 1 := rfl

-- Implicit arguments are also compared up to definitional equality. The indices of `M.comp` form
-- a monoid whose laws are rules, so a composite `M.comp x y : M (e ⬝ e)` can be used at `M e`. The
-- outer implicit index of `(x ⬝ y) ⬝ z` is then `e` rather than the `e ⬝ e` of the rule's
-- left-hand side, but `e ⬝ e ↦ e`.
axiom Ix : Type
axiom Ix.e : Ix
axiom Ix.op : Ix → Ix → Ix
local infixr:70 " ⬝ " => Ix.op
@[rewrite_rule] axiom Ix.e_op (i : Ix) : Ix.e ⬝ i = i
@[rewrite_rule] axiom Ix.op_assoc (i j k : Ix) : (i ⬝ j) ⬝ k = i ⬝ j ⬝ k

axiom M : Ix → Type
axiom M.comp {i j : Ix} : M i → M j → M (i ⬝ j)
@[rewrite_rule] axiom M.comp_assoc {i j k : Ix} (x : M i) (y : M j) (z : M k) :
  M.comp (M.comp x y) z = M.comp x (M.comp y z)

example {k : Ix} (x y : M Ix.e) (z : M k) :
    @M.comp Ix.e k (@M.comp Ix.e Ix.e x y) z = M.comp x (M.comp y z) := rfl

-- Implicit arguments are matched after the explicit ones, and up to definitional equality once
-- their variables are bound. Here the outer index `e ⬝ k` also matches `i ⬝ j` structurally, but
-- with `i := e`, while the explicit argument gives `i := k`.
@[rewrite_rule] axiom Ix.op_e (i : Ix) : i ⬝ Ix.e = i

example {k l : Ix} (x : M k) (y : M Ix.e) (z : M l) :
    @M.comp (Ix.e ⬝ k) l (@M.comp k Ix.e x y) z = M.comp x (M.comp y z) := rfl

-- Later rules take precedence. Associativity also applies to `L (i ⬝ j) ⬝ R (i ⬝ j)`, after
-- unfolding `L (i ⬝ j)` with `L_op`, but the more specific `L_R` is declared later.
axiom L : Ix → Ix
axiom R : Ix → Ix
@[rewrite_rule] axiom L_op (i j : Ix) : L (i ⬝ j) = L i ⬝ L j
@[rewrite_rule] axiom L_R (i : Ix) : L i ⬝ R i = i

example (i j : Ix) : L (i ⬝ j) ⬝ R (i ⬝ j) = i ⬝ j := rfl

-- Applications of the same rule head are unified argument-wise before either side is rewritten.
-- Rewriting `(i ⬝ j) ⬝ k` to `i ⬝ (j ⬝ k)` first would solve `?a ⬝ ?b` with `?a := i`, and then
-- `x : Q (i ⬝ j)` would not fit.
axiom Q : Ix → Type
axiom Q.ext (a b : Ix) : Q a → Q (a ⬝ b)

noncomputable example (i j k : Ix) (x : Q (i ⬝ j)) : Q ((i ⬝ j) ⬝ k) := Q.ext _ _ x

-- Subpatterns are matched after rewriting the target one rule at a time, checking its head after
-- each step. `Ix.e ⬝ Ix.P (i ⬝ j)` reaches the head `Ix.P` after one step; normalizing it further
-- would rewrite `Ix.P (i ⬝ j)` away.
axiom Ix.P : Ix → Ix
axiom Ix.K : Ix → Ix
@[rewrite_rule] axiom Ix.P_op (i j : Ix) : Ix.P (i ⬝ j) = Ix.P i ⬝ Ix.P j
@[rewrite_rule] axiom Ix.K_P (i : Ix) : Ix.K (Ix.P i) = i

example (i j : Ix) : Ix.K (Ix.e ⬝ Ix.P (i ⬝ j)) = i ⬝ j := rfl

-- A target can reach the head of a subpattern more than once while unfolding: `(wrap T).op n`
-- has the head `Str.op`, but with `wrap T` for `T`. Unfolding it further gives `T.op (n + 1)`.
structure Str where
  op : Nat → Nat

axiom G : Str → Nat → Nat
@[rewrite_rule] axiom G_op (T : Str) (n : Nat) : G T (T.op n) = n

def wrap (T : Str) : Str := ⟨fun n => T.op (n + 1)⟩

example (T : Str) (n : Nat) : G T ((wrap T).op n) = n + 1 := rfl

/-! ## Rules on library definitions -/

attribute [rewrite_rule] Nat.zero_add

example (n : Nat) : 0 + n = n := rfl

/-! ## Invalid rules -/

/-- error: invalid rewrite rule `bad₁`: the conclusion must be an equality
  True -/
#guard_msgs in
@[rewrite_rule] axiom bad₁ : True

/--
error: invalid rewrite rule `bad₂`: variable `m` does not occur in a pattern position of the left-hand side
  diff n 0
-/
#guard_msgs in
@[rewrite_rule] axiom bad₂ (n m : Nat) : diff n 0 = m

/--
error: invalid rewrite rule `bad₃`: the head `Nat.succ` is a constructor
  n.succ
-/
#guard_msgs in
@[rewrite_rule] axiom bad₃ (n : Nat) : Nat.succ n = n

axiom H : (Nat → Nat) → Nat

/--
error: invalid rewrite rule `bad₄`: variable `k` does not occur in a pattern position of the left-hand side
  H fun x => k
-/
#guard_msgs in
@[rewrite_rule] axiom bad₄ (k : Nat) : H (fun _ => k) = k

axiom poly.{u} (α : Sort u) : Nat → Nat

-- `v` only occurs in a closed subpattern, which is matched up to defeq rather than bound.
/--
error: invalid rewrite rule `bad₅`: universe parameter `v` is not bound by the left-hand side
  poly (PUnit → Nat) n
-/
#guard_msgs in
@[rewrite_rule] axiom bad₅.{v} (n : Nat) : poly (PUnit.{v} → Nat) n = n

/--
error: invalid rewrite rule `bad₆`: the left-hand side must be an application of a constant
  n
-/
#guard_msgs in
@[rewrite_rule] axiom bad₆ (n : Nat) : n = plus 0 n

/-- error: invalid rewrite rule `plus`: must be a theorem or an axiom -/
#guard_msgs in
attribute [rewrite_rule] plus

/-- error: Invalid attribute scope: Attribute `[rewrite_rule]` must be global, not `local` -/
#guard_msgs in
attribute [local rewrite_rule] diff_self
