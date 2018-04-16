import categories.universal

open categories

universe u₁

variables {C : Type (u₁+1)}
variables [category C]
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

class has_Pullbacks (C : Type (u₁+1)) [category C]:=
  (pullback : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), Pullback f g)

definition pullback [has_Pullbacks C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)  := has_Pullbacks.pullback f g