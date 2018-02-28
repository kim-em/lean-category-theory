-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison
import ...functor

namespace categories.examples.groups
open categories

universe u₁

definition Group : Type (u₁+1) := Σ α : Type u₁, group α

instance group_from_Group (G : Group) : group G.1 := G.2

meta def is_group_hom_obviously := `[unfold is_group_hom, obviously]

structure GroupHomomorphism (G H : Group.{u₁}) : Type u₁ := -- Notice that we push this up one universe level, because our categories expect Obj and Hom at the same universe level.
  (map: G.1 → H.1)
  (is_group_hom : is_group_hom map . is_group_hom_obviously)

local attribute [class] is_group_hom
instance is_group_hom_from_GroupHomomorphism (G H : Group.{u₁}) (f : GroupHomomorphism G H) : is_group_hom f.map := f.is_group_hom

@[simp,ematch] lemma GroupHomomorphism.is_group_hom_lemma (G H : Group) (f : GroupHomomorphism G H) (x y : G.1) : f.map(x * y) = f.map(x) * f.map(y) := by rw f.is_group_hom

definition GroupHomomorphism.identity (G : Group) : GroupHomomorphism G G := ⟨ id ⟩

definition GroupHomomorphism.composition
  {G H K : Group}
  (f: GroupHomomorphism G H) (g: GroupHomomorphism H K) : GroupHomomorphism G K :=
{
  map := λ x, g.map (f.map x),
  is_group_hom := begin 
                    unfold is_group_hom, 
                    dsimp, 
                    intros, 
                    simp,
                  end
}

@[applicable] lemma GroupHomomorphism_pointwise_equality
  {G H : Group}
  (f g : GroupHomomorphism G H)
  (w : ∀ x : G.1, f.map x = g.map x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    have hc : fc = gc := funext w,
    subst hc
end

instance CategoryOfGroups : category Group := {
    Hom := GroupHomomorphism,
    identity := GroupHomomorphism.identity,
    compose  := @GroupHomomorphism.composition
}

end categories.examples.groups
