import Lean

/-!
Tests for controlled unfolding (`@[controlled]`, `unfolding`, `#print unfolding`) and guarded rewrite
rules (`@[guarded_rewrite]`, `rewriting`), after Gratzer, Sterling, Angiuli, Coquand, Birkedal,
"Controlling unfolding in type theory". See `Lean.ControlledUnfolding`.
-/

/-! ## Controlled definitions only unfold within `unfolding` -/

@[controlled] def add : Nat → Nat → Nat
  | 0, n => n
  | m + 1, n => add m n + 1

/--
error: Type mismatch
  Eq.refl n
has type
  n = n
but is expected to have type
  add 0 n = n
-/
#guard_msgs in
example (n : Nat) : add 0 n = n := Eq.refl n

-- Transparency settings do not override the policy.
/--
error: Tactic `rfl` failed: The left-hand side
  add 0 n
is not definitionally equal to the right-hand side
  n

n : Nat
⊢ add 0 n = n
-/
#guard_msgs in
example (n : Nat) : add 0 n = n := by with_unfolding_all rfl

-- Equation lemmas are available everywhere: they are propositional.
example (n : Nat) : add 0 n = n := add.eq_1 n
example (n : Nat) : add 0 n = n := by simp [add]
example (m n : Nat) : add (m + 1) n = add m n + 1 := by rw [add]
example (n : Nat) : add 0 n = n := by unfold add; rfl

-- `delta` expands definitions without equation lemmas, so it is subject to the policy.
/--
error: Tactic `delta` failed: did not delta reduce [add]

n : Nat
⊢ add 0 n = n
-/
#guard_msgs in
example (n : Nat) : add 0 n = n := by delta add; rfl

unfolding add in
theorem add_zero_left (n : Nat) : add 0 n = n := rfl

section
unfolding add
theorem add_succ_left (m n : Nat) : add (m + 1) n = add m n + 1 := rfl
theorem add_two (n : Nat) : add 2 n = n + 2 := rfl
end

-- The section scope has ended.
/--
error: Type mismatch
  Eq.refl (add m n + 1)
has type
  add m n + 1 = add m n + 1
but is expected to have type
  add (m + 1) n = add m n + 1
-/
#guard_msgs in
example (m n : Nat) : add (m + 1) n = add m n + 1 := Eq.refl (add m n + 1)

-- Only controlled definitions can be unfolded.
/--
error: `Nat.add` is not controlled, so it unfolds everywhere; mark it `@[controlled]`
-/
#guard_msgs in
unfolding Nat.add in
example : True := trivial

/--
info: `Nat.add` has no unfolding policy, it unfolds everywhere
-/
#guard_msgs in
#print unfolding Nat.add

/--
error: invalid `@[controlled]`, `notADef` is not a definition
-/
#guard_msgs in
@[controlled] theorem notADef : True := trivial

/-! ## Declarations checked under `unfolding` are abbreviations of their scope -/

unfolding add in
def three : Nat := add 1 2

/--
info: `three` is an abbreviation, it unfolds where all of these unfold: `add`
-/
#guard_msgs in
#print unfolding three

-- `three` would expose the definition of `add`, so it does not unfold outside the scope.
/--
error: Type mismatch
  Eq.refl 3
has type
  3 = 3
but is expected to have type
  three = 3
-/
#guard_msgs in
example : three = 3 := Eq.refl 3

unfolding add in
example : three = 3 := rfl

/-! ## `unfolding` applies to bodies, not to types -/

inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

unfolding add in
@[controlled] def append : Vec α m → Vec α n → Vec α (add m n)
  | .nil,      v => v
  | .cons a u, v => .cons a (append u v)

/--
info: `append` is controlled, it unfolds under `unfolding append`, which also unfolds `add`
-/
#guard_msgs in
#print unfolding append

/--
info: `add` is controlled, it unfolds under `unfolding add`
-/
#guard_msgs in
#print unfolding add

-- The statement is not well-typed without unfolding `add`.
/--
error: Type mismatch
  u
has type
  Vec α n
but is expected to have type
  Vec α (add 0 n)
-/
#guard_msgs in
unfolding add in
theorem append_nil_left_bad {α : Type} {n : Nat} (u : Vec α n) : append .nil u = u := sorry

-- The term form can be used in the statement; `unfolding append` also unfolds `add`.
theorem append_nil_left {α : Type} {n : Nat} (u : Vec α n) :
    unfolding add in (append .nil u = u) :=
  unfolding append in rfl

-- The tactic form.
theorem append_nil_left' {α : Type} {n : Nat} (u : Vec α n) :
    unfolding add in (append .nil u = u) := by
  unfolding append in rfl

-- Non-propositional terms are hoisted into definitions.
def castZeroAdd {α : Type} {n : Nat} (v : Vec α (add 0 n)) : Vec α n :=
  unfolding add in v

/--
error: Type mismatch
  v
has type
  Vec α (add 0 n)
but is expected to have type
  Vec α n
-/
#guard_msgs in
def castZeroAdd' {α : Type} {n : Nat} (v : Vec α (add 0 n)) : Vec α n := v

/-! ## Guarded rewrite rules only fire within `rewriting` -/

unfolding add in
@[guarded_rewrite] theorem add_zero_right (n : Nat) : add n 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· + 1) ih

/--
info: `add_zero_right` is a guarded rewrite rule, it fires under `rewriting add_zero_right`; it was proved under `add`
-/
#guard_msgs in
#print unfolding add_zero_right

/--
error: Type mismatch
  v
has type
  Vec α (add n 0)
but is expected to have type
  Vec α n
-/
#guard_msgs in
def dropZero' {α : Type} {n : Nat} (v : Vec α (add n 0)) : Vec α n := v

rewriting add_zero_right in
def dropZero {α : Type} {n : Nat} (v : Vec α (add n 0)) : Vec α n := v

example (n : Nat) : add n 0 = n := rewriting add_zero_right in rfl
example (n : Nat) : add n 0 = n := by rewriting add_zero_right in rfl

-- `add_zero_right` is not a controlled definition, and `add` is not a rule.
/--
error: `add_zero_right` is a guarded rewrite rule; use `rewriting` instead
-/
#guard_msgs in
unfolding add_zero_right in
example : True := trivial

/--
error: `add` is not a guarded rewrite rule; mark it `@[guarded_rewrite]`
-/
#guard_msgs in
rewriting add in
example : True := trivial

/-! ## The kernel enforces the policy on its own -/

section
open Lean

private def mkAddZeroDecl (name : Name) : Declaration :=
  -- `∀ n, add 0 n = n`, proved by `fun n => Eq.refl n`
  let nat := mkConst ``Nat
  .thmDecl {
    name, levelParams := []
    type := mkForall `n .default nat <|
      mkApp3 (mkConst ``Eq [1]) nat (mkApp2 (mkConst ``add) (mkNatLit 0) (.bvar 0)) (.bvar 0)
    value := mkLambda `n .default nat <| mkApp2 (mkConst ``Eq.refl [1]) nat (.bvar 0)
  }

/--
error: (kernel) declaration type mismatch, 'kernelAddZeroBad' has type
  ∀ (n : Nat), n = n
but it is expected to have type
  ∀ (n : Nat), add 0 n = n
-/
#guard_msgs in
run_meta addDecl (mkAddZeroDecl `kernelAddZeroBad)

run_meta withUnfoldings #[``add] <| addDecl (mkAddZeroDecl `kernelAddZero)

private def mkAddZeroRightDecl (name : Name) : Declaration :=
  -- `∀ n, add n 0 = n`, proved by `fun n => Eq.refl n`, which needs the rule `add_zero_right`
  let nat := mkConst ``Nat
  .thmDecl {
    name, levelParams := []
    type := mkForall `n .default nat <|
      mkApp3 (mkConst ``Eq [1]) nat (mkApp2 (mkConst ``add) (.bvar 0) (mkNatLit 0)) (.bvar 0)
    value := mkLambda `n .default nat <| mkApp2 (mkConst ``Eq.refl [1]) nat (.bvar 0)
  }

/--
error: (kernel) declaration type mismatch, 'kernelAddZeroRightBad' has type
  ∀ (n : Nat), n = n
but it is expected to have type
  ∀ (n : Nat), add n 0 = n
-/
#guard_msgs in
run_meta addDecl (mkAddZeroRightDecl `kernelAddZeroRightBad)

run_meta withUnfoldings #[``add_zero_right] <| addDecl (mkAddZeroRightDecl `kernelAddZeroRight)

end
