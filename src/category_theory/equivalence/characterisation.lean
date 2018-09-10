-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.equivalence
import category_theory.natural_isomorphism

open category_theory

namespace category_theory.equivalence

universes u₁ u₂

variables {C : Type (u₁+1)} [large_category C] {D : Type (u₂+1)} [large_category D]

def ess_surj_on_equivalence (e : C ≌ D) : ess_surj (e.functor) :=
⟨ λ Y : D, e.inverse Y, λ Y : D, (e.inv_fun_id Y) ⟩

instance faithful_of_equivalence (F : C ⥤ D) [is_equivalence F] : faithful (F) := 
{ injectivity' := λ X Y f g w, begin  
                                have p := congr_arg (@category_theory.functor.map _ _ _ _ F.inv _ _) w,
                                rw is_equivalence.inv_fun_map at p,
                                rw is_equivalence.inv_fun_map at p,
                                simp at p,
                                exact p
                              end }.


def full_of_equivalence (e : equivalence C D) : full (e.functor) := 
{ preimage := λ X Y f, (e.fun_inv_id X).inv ≫ (e.inverse.map f) ≫ (e.fun_inv_id Y).hom,
  witness' := λ X Y f, begin
                        apply (equivalence.faithful_of_equivalence e.inverse).injectivity',
                        obviously,
                      end }

section
private meta def faithfulness := `[apply faithful.injectivity'] 
local attribute [tidy] faithfulness

-- FIXME improve API for ess_surj
def equivalence_inverse (F : C ⥤ D) [full F] [faithful : faithful F] [es : ess_surj F] : D ⥤ C := 
{ obj  := λ X, (ess_surj.pre.{u₁+1 u₁} F X),
  map' := λ X Y f, preimage F ((ess_surj.iso.{u₁+1 u₁} F X).hom ≫ f ≫ (ess_surj.iso.{u₁+1 u₁} F Y).inv) }

-- FIXME pure boilerplate...
@[simp] lemma equivalence_inverse_map 
  (F : C ⥤ D) [full F] [faithful : faithful F] [es : ess_surj F]
  {X Y : D} (f : X ⟶ Y) : (equivalence_inverse F).map f = preimage F ((ess_surj.iso.{u₁+1 u₁} F X).hom ≫ f ≫ (ess_surj.iso.{u₁+1 u₁} F Y).inv) := rfl

def equivalence_of_fully_faithfully_ess_surj (F : C ⥤ D) [full F] [faithful : faithful F] [es : ess_surj F] : is_equivalence F := 
{ inverse := equivalence_inverse F,
  fun_inv_id' := nat_iso.from_components (λ X, preimage_iso (ess_surj.iso F (F X))) (by obviously), 
  inv_fun_id' := nat_iso.from_components (λ Y, (ess_surj.iso F Y))                  (by obviously) }
end

end category_theory.equivalence