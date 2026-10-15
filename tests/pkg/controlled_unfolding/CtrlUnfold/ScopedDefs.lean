import CtrlUnfold.Defs

/-! Namespace-level `scoped unfolding` and `scoped rewriting`, used by `CtrlUnfold.ScopedUse`. -/

namespace Arith

scoped unfolding add
scoped rewriting add_zero_right

-- Both are active in the rest of the namespace.
example (n : Nat) : add 0 n = n := rfl
example (n : Nat) : add n 0 = n := rfl

-- Values checked in the namespace only unfold where the namespace's names are active.
def addZero (n : Nat) : Nat := add n 0

-- Types are still checked under an empty active set.
/--
error: Type mismatch
  v
has type
  Fin n
but is expected to have type
  Fin (add n 0)
-/
#guard_msgs in
theorem typeBad {n : Nat} (v : Fin n) : (v : Fin (add n 0)) = v := sorry

end Arith

-- Outside of the namespace, neither is active.
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

/-- error: Scoped attributes must be used inside namespaces -/
#guard_msgs in
scoped unfolding add
