import Lean
import LocalRw.Defs

/-! Checks that definitions with local rewrite rules can be instantiated in another module. -/

def natRec (P : Nat → Type) (z : P 0) (s : (n : Nat) → P n → P (n + 1)) (n : Nat) : P n :=
  Nat.rec (motive := P) z s n

def natAdd := add Nat 0 Nat.succ natRec

example : natAdd 2 3 = 5 := rfl

theorem two_add (n : Nat) : natAdd 2 n = n + 2 := succ_succ_add Nat 0 Nat.succ natRec n

/-- error: (kernel) invalid occurrence of 'add', it has local rewrite rule parameters and must be applied to at least 6 arguments -/
#guard_msgs in
open Lean Meta in
run_meta addDecl <| .defnDecl {
  name := `bareAdd, levelParams := [], hints := .opaque, safety := .safe
  type := (← inferType (mkConst ``add))
  value := mkConst ``add }
