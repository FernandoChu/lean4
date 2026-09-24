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
error: invalid rewrite rule `bad₄`: pattern variables may only occur as arguments of constant applications, but the left-hand side contains the pattern
  fun x => k
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
