import ..abelian.abelian
import category_theory.universal.zero


open category_theory
open category_theory.limits

universes u v

class projective {C : Type u} [category.{u v} C] (P : C) :=
(lift : Π M N : C, Π f : M ⟶ N, Π w : epi f, Π g : P ⟶ N, P ⟶ M)
(factorisation : Π M N : C, Π f : M ⟶ N, Π w : epi f, Π g : P ⟶ N, (lift M N f w g) ≫ f = g)

structure projective_cover {C : Type u} [category.{u v} C] (X : C) :=
(cover : C)
(map : cover ⟶ X)
(projectivity: projective cover)
(surjectivity: epi map)

class enough_projectives (C : Type u) [category.{u v} C]  :=
(cover : Π X : C, projective_cover X)

structure chain_complex (C : Type u) [category.{u v} C] [has_zero_object.{u v} C] :=
(objects : ℤ → C)
(d : Π i : ℤ, objects i ⟶ objects (i + 1))
(d_squared : Π i, (d i) ≫ (d (i+1)) = zero_morphism _ _)

structure projective_resolution {C : Type u} [category.{u v} C] [has_zero_object.{u v} C] (X : C) :=
(complex : chain_complex C)
(projectivity : Π i : ℤ, i < 0 → projective (complex.objects i))
(of : complex.objects 0 = X)
(nothing : Π i : ℤ, i > 0 → complex.objects i = zero_object.{u v} C) -- it's zero

-- TODO find out why we don't also need universe annotations on `enough_projectives`?
-- TODO this needs the category to be abelian!
def construct_injective_resolution {C : Type u} [category.{u v} C] [has_zero_object.{u v} C] [enough_projectives C] (X : C) : projective_resolution X := sorry
-- we define the complex inductively, taking the cover of X, then the cover of its kernel, and so on

/-
Baer's criterion:
A (right) R-module E is injective iff for every right ideal J ⊂ R, every map J → E extends to a map R → E

The forward direction is immediate from the definition. The reverse direction is harder, and uses Zorn.
-/

-- Corollary: If R is a PID, then an R-module A is injective iff it is 'divisible': ∀ r ∈ R, r ≠ 0, ∀ a ∈ A, ∃ b ∈ A so a = b * r.

/- Lemmas:

M is projective iff Hom_A(M ⟶ -) is exact
M is projective in A iff M is injective in Aᵒᵖ
M is injective iff Hom_A(- ⟶ M) is exact
-/

-- Comparision theorem: a map lifts to a chain map between resolutions, which is unique up to homotopy

-- If R : D → C is additive, L : C → D is exact, and L ⊣ R, then R preserves injectives.

