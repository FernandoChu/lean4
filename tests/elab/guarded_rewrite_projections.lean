/-! Guarded rewrite rules whose left-hand sides use projection functions. -/

class Cat' (obj : Type) where
  Hom : obj → obj → Type
  id : ∀ X, Hom X X
  comp : ∀ {X Y Z}, Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y} (f : Hom X Y), comp (id X) f = f

@[guarded_rewrite] theorem id_comp_rule {C : Type} [Cat' C] {X Y : C} (f : Cat'.Hom X Y) :
    Cat'.comp (Cat'.id X) f = f :=
  Cat'.id_comp f

structure Fn (C D : Type) [Cat' C] [Cat' D] where
  obj : C → D
  map : ∀ {X Y : C}, Cat'.Hom X Y → Cat'.Hom (obj X) (obj Y)
  map_id : ∀ X, map (Cat'.id X) = Cat'.id (obj X)

@[guarded_rewrite] theorem map_id_rule {C D : Type} [Cat' C] [Cat' D] (F : Fn C D) (X : C) :
    F.map (Cat'.id X) = Cat'.id (F.obj X) :=
  F.map_id X

variable {C D : Type} [Cat' C] [Cat' D]

/-! Patterns are matched by unfolding one step at a time: unfolding `myId X` all the way would turn
`Cat'.id X` into a primitive projection of the instance, which the pattern does not match. -/

def myId (X : C) : Cat'.Hom X X := Cat'.id X

rewriting id_comp_rule in
example {X Y : C} (f : Cat'.Hom X Y) : Cat'.comp (myId X) f = f := rfl

/-! The kernel also applies rules to stuck primitive projections. Structure eta for `Fn` compares
the type of `map_id`, where `map` is the primitive projection `F.2`, with one stated using `F.map`,
which `map_id_rule` rewrites. -/

def Fn.id' (F : Fn C D) : Fn C D := ⟨F.obj, F.map, F.map_id⟩

rewriting map_id_rule in
example (F : Fn C D) : F.id' = F := rfl

/-! Nested proofs whose statements are only well typed under the active set stay inline: the kernel
checks the statements of auxiliary theorems under an empty active set. -/

inductive Over (F : Fn C D) (X : C) : Cat'.Hom (F.obj X) (F.obj X) → Type where
  | mk (g : Cat'.Hom (F.obj X) (F.obj X)) : Over F X g

structure Sec (F : Fn C D) (X : C) where
  o : Over F X (Cat'.id (F.obj X))
  h : o = o

-- The proof of `h` has type `Over.mk (F.map (Cat'.id X)) = …` at `Over F X (Cat'.id (F.obj X))`.
rewriting map_id_rule in
def sec (F : Fn C D) (X : C) : Sec F X := ⟨.mk (F.map (Cat'.id X)), rfl⟩
