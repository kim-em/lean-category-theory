-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import categories.equivalence

open category_theory

namespace category_theory.equivalence

universes u₁ u₂

variable {C : Type (u₁+1)}
variable [large_category C]
variable {D : Type (u₂+1)}
variable [large_category D]


def Equivalences_are_EssentiallySurjective (e : Equivalence C D) : EssentiallySurjective (e.functor) :=
  λ Y : D, ⟨ e.inverse Y, e.isomorphism_2.components Y ⟩

def Equivalences_are_Faithful (e : Equivalence C D) : faithful (e.functor) := 
{ injectivity := λ X Y f g w, begin  
                                have p := congr_arg (@category_theory.functor.map _ _ _ _ e.inverse  _ _) w,
                                simp at p,                                     
                                exact p 
                              end }


def Equivalences_are_Full (e : Equivalence C D) : full (e.functor) := 
{ preimage := λ X Y f, (e.isomorphism_1.components X).inv ≫ (e.inverse.map f) ≫ (e.isomorphism_1.components Y).hom,
  witness := λ X Y f, begin
                        apply (Equivalences_are_Faithful e.symm).injectivity,
                        tidy,
                        rewrite_search_using [`ematch] /- { view := visualiser, exhaustive := tt }-/,   
                        -- obviously_vis,
                      end }

section
private meta def faithfulness := `[apply faithful.injectivity] -- This is a bit dicey.
local attribute [tidy] faithfulness

-- TODO: weirdly, failing to name `faithful` causes an error.
def Fully_Faithful_EssentiallySurjective_Functor_inverse (F : C ↝ D) [full F] [faithful : faithful F] [es : EssentiallySurjective F] : D ↝ C := 
{ obj  := λ X, (es X).1,
  map' := λ X Y f, preimage F ((es X).2.hom ≫ f ≫ (es Y).2.inv) }

def Fully_Faithful_EssentiallySurjective_Functor_is_Equivalence (F : C ↝ D) [full F] [faithful : faithful F] [es : EssentiallySurjective F] : is_Equivalence F := 
{ inverse := Fully_Faithful_EssentiallySurjective_Functor_inverse F,
  isomorphism_1 := NaturalIsomorphism.from_components (λ X, preimage_iso (es (F X)).2) (by obviously), 
  isomorphism_2 := NaturalIsomorphism.from_components (λ Y, (es Y).2)                  (by obviously) }
end

-- TODO
instance (F : C ↝ D) [is_Equivalence F] : full F     := sorry
instance (F : C ↝ D) [is_Equivalence F] : faithful F := sorry

end category_theory.equivalence