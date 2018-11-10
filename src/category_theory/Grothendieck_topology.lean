import category_theory.limits
import category_theory.over

open category_theory
open category_theory.limits

universes u₁ v₁

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞 
variables {X Y : C}

structure cover (X : C) :=
(I : Type)
(U : I → C)
(π : Π i : I, U i ⟶ X)

def pullback_cover [has_pullbacks.{u₁ v₁} C] {X Y : C} (c : cover.{u₁ v₁} X) (f : Y ⟶ X) : cover.{u₁ v₁} Y :=
{ I := c.I,
  U := λ i, (pullback (c.π i) f),
  π := λ i, (pullback.square (c.π i) f).π₂ }

def covers_of_cover {X : C} (c : cover.{u₁ v₁} X) (d : Π i : c.I, cover.{u₁ v₁} (c.U i)) : cover.{u₁ v₁} X :=
{ I := Σ i : c.I, (d i).I,
  U := λ i, (d i.1).U i.2,
  π := λ i, ((d i.1).π i.2) ≫ (c.π i.1) }

def singleton_cover {Y X : C} (f : Y ⟶ X) : cover.{u₁ v₁} X :=
{ I := unit,
  U := λ i, Y,
  π := λ i, f }

structure Grothendieck_topology [has_pullbacks.{u₁ v₁} C] :=
(covers (X : C) : set (cover.{u₁ v₁} X))
(pullback {X : C} (c ∈ covers X) {Y : C} (f : Y ⟶ X) : pullback_cover c f ∈ covers Y)
(cover_of_covers {X : C} (c ∈ covers X) (d : Π (i : cover.I.{u₁ v₁} c), {P | covers (c.U i) P}) : 
  covers_of_cover c (λ i, (d i).1) ∈ covers X)
(isomorphism_cover {Y X : C} (f : Y ≅ X) : singleton_cover (f.hom) ∈ covers X)

-- structure site (C : Type u₁) 


-- Or, we could do this in terms of sieves:
structure sieve (X : C) :=
(S : set (over.{u₁ v₁} X))
(closed (f : { f // S f }) {Z : C} (g : Z ⟶ f.1.1) : (⟨ Z, g ≫ f.val.2 ⟩ : over X) ∈ S) 

-- example : a topology is a Grothendieck topology

-- example : etale maps over a scheme X, with covers jointly surjective (U_i ⟶ X)_i