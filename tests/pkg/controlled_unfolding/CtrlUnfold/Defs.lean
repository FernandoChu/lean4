/-! Declares controlled definitions and a guarded rewrite rule that `CtrlUnfold.Use` imports. -/

@[controlled] def add : Nat → Nat → Nat
  | 0, n => n
  | m + 1, n => add m n + 1

unfolding add in
def three : Nat := add 1 2

unfolding add in
@[guarded_rewrite] theorem add_zero_right (n : Nat) : add n 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· + 1) ih
