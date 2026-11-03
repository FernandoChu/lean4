This is an experimental fork of **Lean 4** that adds user-declared definitional rewrite rules, in the style of Agda's rewrite rules. Neither confluence nor termination of the rules is checked, so they can make type checking loop or (further) break subject reduction.

# Fork features

## Global rewrite rules: `@[rewrite_rule]`

Tagging a theorem or axiom `∀ xs, f ps = rhs` with `@[rewrite_rule]` turns `f ps ↦ rhs` into a reduction rule used by both the elaborator and the kernel, like Agda's `{-# REWRITE #-}` pragma.

```lean
def plus : Nat → Nat → Nat
  | n, .zero => n
  | n, .succ m => .succ (plus n m)

theorem plus_zero_left : ∀ n, plus .zero n = n
  | .zero => rfl
  | .succ n => congrArg Nat.succ (plus_zero_left n)

attribute [rewrite_rule] plus_zero_left

example (n : Nat) : plus .zero n = n := rfl
```

The left-hand side must be headed by a constant that is neither an inductive type nor a constructor. The kernel does not trust the elaborator's copy of a rule: it re-derives each rule from the type of the tagged declaration. See `src/Lean/RewriteRules.lean` for the accepted patterns.

## Local rewrite rules: `LocalRewrite`

A parameter `h : LocalRewrite (∀ xs, g ps = rhs)` of a declaration, where `g` is an earlier parameter, makes `g ps ↦ rhs` a reduction rule while checking the rest of that declaration. This follows Leray and Winterhalter's Local Rewriting Type Theory ("Encode the Cake and Eat It Too", POPL 2026) and Agda's `@rewrite` module parameters. Section `variable`s work too:

```lean
variable (N : Type) (zero : N) (succ : N → N)
  (rec : (P : N → Type) → P zero → ((n : N) → P n → P (succ n)) → (n : N) → P n)
  {rec_zero : LocalRewrite (∀ P z s, rec P z s zero = z)}
  {rec_succ : LocalRewrite (∀ P z s n, rec P z s (succ n) = s n (rec P z s n))}

def add (n m : N) : N := rec (fun _ => N) m (fun _ => succ) n

theorem succ_succ_add (n : N) :
    add N zero succ rec (succ (succ zero)) n = succ (succ n) := rfl
```

Every use of such a declaration must apply it at least up to its last `LocalRewrite` parameter, and the kernel checks that each `LocalRewrite` argument holds *definitionally*. Implicit ones are filled in automatically when they do, e.g. `add Nat 0 Nat.succ (fun P z s n => Nat.rec (motive := P) z s n)`. Instantiating the rules therefore never needs an axiom. A `LocalRewrite` hypothesis introduced by `fun` or `intro` is not a rule.

Tests: `tests/elab/rewrite_rules.lean`, `tests/elab/local_rewrite_rules.lean`, `tests/pkg/rewrite_rules` and `tests/pkg/local_rewrite_rules`.

# Building from Source

The fork's features are on the `local-rewrite-rules` branch:

```bash
git clone -b local-rewrite-rules https://github.com/FernandoChu/lean4
cd lean4
cmake --preset release
make -C build/release -j$(nproc || sysctl -n hw.logicalcpu)
```

This puts the `lean` and `lake` binaries in `build/release/stage1/bin`. See [Building Lean](doc/make/index.md) for dependencies, platform-specific setup and editor integration.
