import Lean
import RwRules.Defs

/-! Checks that rewrite rules declared in an imported module are used by the elaborator and kernel. -/

theorem plus_zero_left' (n : Nat) : plus .zero n = n := rfl

theorem rec_base' (b : Nat) (l : b = b) : Circle.rec b l Circle.base = b := rfl

open Lean in
run_meta addDecl <| .thmDecl {
  name := `kernelOnly, levelParams := []
  type := mkForall `n .default (mkConst ``Nat) <|
    mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkApp2 (mkConst ``plus) (mkConst ``Nat.zero) (.bvar 0)) (.bvar 0)
  value := mkLambda `n .default (mkConst ``Nat) <| mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (.bvar 0)
}
