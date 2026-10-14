import Lean
import CtrlUnfold.Defs

/-! Checks that unfolding policies declared in an imported module are respected by the elaborator and kernel. -/

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

unfolding add in
example (n : Nat) : add 0 n = n := rfl

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

rewriting add_zero_right in
example (n : Nat) : add n 0 = n := rfl

example (n : Nat) : add 0 n = n := by simp [add]

open Lean in
private def mkAddZeroDecl (name : Name) : Declaration :=
  .thmDecl {
    name, levelParams := []
    type := mkForall `n .default (mkConst ``Nat) <|
      mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkApp2 (mkConst ``add) (mkNatLit 0) (.bvar 0)) (.bvar 0)
    value := mkLambda `n .default (mkConst ``Nat) <| mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (.bvar 0)
  }

/--
error: (kernel) declaration type mismatch, 'kernelBad' has type
  ∀ (n : Nat), n = n
but it is expected to have type
  ∀ (n : Nat), add 0 n = n
-/
#guard_msgs in
run_meta Lean.addDecl (mkAddZeroDecl `kernelBad)

run_meta Lean.withUnfoldings #[``add] <| Lean.addDecl (mkAddZeroDecl `kernelGood)
