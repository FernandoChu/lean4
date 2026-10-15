import CtrlUnfold.ScopedDefs

/-! Checks that namespace-level activations are restored by `open` and `namespace` after import. -/

/--
error: Type mismatch
  Eq.refl n
has type
  n = n
but is expected to have type
  add n 0 = n
-/
#guard_msgs in
example (n : Nat) : add n 0 = n := Eq.refl n

/--
error: Type mismatch
  Eq.refl n
has type
  n = n
but is expected to have type
  Arith.addZero n = n
-/
#guard_msgs in
example (n : Nat) : Arith.addZero n = n := Eq.refl n

open Arith in
example (n : Nat) : add n 0 = n := rfl

open Arith in
example (n : Nat) : addZero n = n := rfl

section
open Arith
example (n : Nat) : add 0 n = n := rfl
end

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

namespace Arith
example (n : Nat) : add n 0 = n := rfl
end Arith
