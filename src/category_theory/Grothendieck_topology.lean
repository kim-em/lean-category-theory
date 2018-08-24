import category_theory.universal.limits

open category_theory
open category_theory.universal

universe u₁

variables {C : Type (u₁+1)}
variables [large_category C]
variables {X Y : C}

structure cover {C : Type (u₁+1)} [large_category C] (X : C) :=
(I : Type)
(U : I → C)
(π : Π i : I, U i ⟶ X)

def pullback_cover [has_pullbacks.{u₁+1 u₁} C] {X Y : C} (c : cover X) (f : Y ⟶ X) : cover Y :=
{ I := c.I,
  U := λ i, (pullback (c.π i) f),
  π := λ i, (pullback.square (c.π i) f).π₂ }

def covers_of_cover {X : C} (c : cover X) (d : Π i : c.I, cover (c.U i)) : cover X :=
{ I := Σ i : c.I, (d i).I,
  U := λ i, (d i.1).U i.2,
  π := λ i, ((d i.1).π i.2) ≫ (c.π i.1) }

def singleton_cover {Y X : C} (f : Y ⟶ X) : cover X :=
{ I := unit,
  U := λ i, Y,
  π := λ i, f }

structure GrothendieckTopology [has_pullbacks.{u₁+1 u₁} C] :=
(covers : Π (X : C), set (cover X))
(pullback : Π {X : C} (c ∈ covers X) {Y : C} (f : Y ⟶ X), pullback_cover c f ∈ covers Y)
(cover_of_covers : Π {X : C} (c ∈ covers X) (d : Π (i : cover.I c), {P | covers (c.U i) P}), covers_of_cover c (λ i, (d i).1) ∈ covers X)
(isomorphism_cover : Π {Y X : C} (f : Y ≅ X), singleton_cover f.hom ∈ covers X)

-- example : a topology is a Grothendieck topology

-- example : etale maps over a scheme X, with covers jointly surjective (U_i ⟶ X)_i