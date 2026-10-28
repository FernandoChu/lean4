/-! Declares definitions with local rewrite rules that `LocalRw.Use` instantiates after importing this module. -/

section
variable (N : Type) (zero : N) (succ : N → N)
  (rec : (P : N → Type) → P zero → ((n : N) → P n → P (succ n)) → (n : N) → P n)
  {rec_zero : LocalRewrite (∀ P z s, rec P z s zero = z)}
  {rec_succ : LocalRewrite (∀ P z s n, rec P z s (succ n) = s n (rec P z s n))}

def add (n m : N) : N := rec (fun _ => N) m (fun _ => succ) n

theorem succ_succ_add (n : N) :
    add N zero succ rec (succ (succ zero)) n = succ (succ n) := rfl
end
