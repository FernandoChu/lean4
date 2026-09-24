/-! Declares rewrite rules that `RwRules.Use` relies on after importing this module. -/

def plus : Nat → Nat → Nat
  | n, .zero => n
  | n, .succ m => .succ (plus n m)

@[rewrite_rule]
theorem plus_zero_left : ∀ n, plus .zero n = n
  | .zero => rfl
  | .succ n => congrArg Nat.succ (plus_zero_left n)

axiom Circle : Type
axiom Circle.base : Circle
axiom Circle.rec {α : Sort u} (b : α) (l : b = b) : Circle → α

@[rewrite_rule]
axiom Circle.rec_base {α : Sort u} (b : α) (l : b = b) : Circle.rec b l Circle.base = b
