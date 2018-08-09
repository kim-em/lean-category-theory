import categories.universal

open category_theory

universe u₁

variables {C : Type (u₁+1)}
variables [large_category C]
variables {X Y : C}

structure Pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
(pullback            : C)
(left_morphism       : pullback ⟶ X)
(right_morphism      : pullback ⟶ Y)
(commutes            : left_morphism ≫ f = right_morphism ≫ g)
(map                 : ∀ {P : C} (l : P ⟶ X) (r : P ⟶ Y) (h : l ≫ f = r ≫ g), P ⟶ pullback)
(left_factorisation  : ∀ {P : C} (l : P ⟶ X) (r : P ⟶ Y) (h : l ≫ f = r ≫ g), map l r h ≫ left_morphism = l)
(right_factorisation : ∀ {P : C} (l : P ⟶ X) (r : P ⟶ Y) (h : l ≫ f = r ≫ g), map l r h ≫ right_morphism = r)
(uniqueness          : ∀ {P : C} (l : P ⟶ X) (r : P ⟶ Y) (h : l ≫ f = r ≫ g) (p q : P ⟶ pullback) (hpl : p ≫ left_morphism = l) (hql : q ≫ left_morphism = l) (hpr : p ≫ right_morphism = r) (hqr : q ≫ right_morphism = r) , p = q)

class has_Pullbacks (C : Type (u₁+1)) [large_category C]:=
  (pullback : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), Pullback f g)

definition pullback [has_Pullbacks C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)  := has_Pullbacks.pullback f g

structure Cover {C : Type (u₁+1)} [large_category C] (X : C) :=
(I : Type)
(U : I → C)
(π : Π i : I, U i ⟶ X)

definition pullback_cover [has_Pullbacks C] {X Y : C} (c : Cover X) (f : Y ⟶ X) : Cover Y :=
{ I := c.I,
  U := λ i, (pullback (c.π i) f).pullback,
  π := λ i, (pullback (c.π i) f).right_morphism }

definition covers_of_cover {X : C} (c : Cover X) (d : Π i : c.I, Cover (c.U i)) : Cover X :=
{ I := Σ i : c.I, (d i).I,
  U := λ i, (d i.1).U i.2,
  π := λ i, ((d i.1).π i.2) ≫ (c.π i.1) }

definition singleton_cover {Y X : C} (f : Y ⟶ X) : Cover X :=
{ I := unit,
  U := λ i, Y,
  π := λ i, f }

structure GrothendieckTopology [has_Pullbacks C] :=
(covers : Π (X : C), set (Cover X))
(pullback : Π {X : C} (c ∈ covers X) {Y : C} (f : Y ⟶ X), pullback_cover c f ∈ covers Y)
(cover_of_covers : Π {X : C} (c ∈ covers X) (d : Π (i : Cover.I c), {P | covers (c.U i) P}), covers_of_cover c (λ i, (d i).1) ∈ covers X)
(isomorphism_cover : Π {Y X : C} (f : Y ≅ X), singleton_cover f.map ∈ covers X)

-- example : a topology is a Grothendieck topology

-- example : etale maps over a scheme X, with covers jointly surjective (U_i ⟶ X)_i