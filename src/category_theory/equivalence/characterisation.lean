-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.equivalence
import category_theory.natural_isomorphism

open category_theory

namespace category_theory.equivalence

universes u₁ u₂

variables {C : Type (u₁+1)} [large_category C] {D : Type (u₂+1)} [large_category D]

def Equivalences_are_EssentiallySurjective (e : Equivalence C D) : ess_surj (e.functor) :=
⟨ λ Y : D, e.inverse Y, λ Y : D, (e.isomorphism_2 Y) ⟩

lemma Equivalences_are_Faithful (e : Equivalence C D) : faithful (e.functor) := 
{ injectivity' := λ X Y f g w, begin  
                                have p := congr_arg (@category_theory.functor.map _ _ _ _ e.inverse  _ _) w,
                                simp at p,
                                exact p
                              end }.


def Equivalences_are_Full (e : Equivalence C D) : full (e.functor) := 
{ preimage := λ X Y f, (e.isomorphism_1 X).inv ≫ (e.inverse.map f) ≫ (e.isomorphism_1 Y).hom,
  witness' := λ X Y f, begin
                        apply (Equivalences_are_Faithful e.symm).injectivity',
                        obviously,
                      end }

section
private meta def faithfulness := `[apply faithful.injectivity'] 
local attribute [tidy] faithfulness

-- FIXME improve API for ess_surj
def Fully_Faithful_EssentiallySurjective_Functor_inverse (F : C ↝ D) [full F] [faithful : faithful F] [es : ess_surj F] : D ↝ C := 
{ obj  := λ X, (ess_surj.pre.{u₁+1 u₁} F X),
  map' := λ X Y f, preimage F ((ess_surj.iso.{u₁+1 u₁} F X).hom ≫ f ≫ (ess_surj.iso.{u₁+1 u₁} F Y).inv) }

-- FIXME pure boilerplate...
@[simp] lemma Fully_Faithful_EssentiallySurjective_Functor_inverse_map 
  (F : C ↝ D) [full F] [faithful : faithful F] [es : ess_surj F]
  {X Y : D} (f : X ⟶ Y) : (Fully_Faithful_EssentiallySurjective_Functor_inverse F).map f = preimage F ((ess_surj.iso.{u₁+1 u₁} F X).hom ≫ f ≫ (ess_surj.iso.{u₁+1 u₁} F Y).inv) := rfl

def Fully_Faithful_EssentiallySurjective_Functor_is_Equivalence (F : C ↝ D) [full F] [faithful : faithful F] [es : ess_surj F] : is_Equivalence F := 
{ inverse := Fully_Faithful_EssentiallySurjective_Functor_inverse F,
  isomorphism_1' := nat_iso.from_components (λ X, preimage_iso (ess_surj.iso F (F X))) (by obviously), 
  isomorphism_2' := nat_iso.from_components (λ Y, (ess_surj.iso F Y))                  (by obviously) }
end

-- TODO
instance (F : C ↝ D) [is_Equivalence F] : full F     := sorry
instance (F : C ↝ D) [is_Equivalence F] : faithful F := sorry

end category_theory.equivalence