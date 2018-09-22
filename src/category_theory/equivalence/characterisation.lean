-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.equivalence
import category_theory.natural_isomorphism

open category_theory

namespace category_theory.equivalence

universes u₁ u₂

variables {C : Type (u₁+1)} [large_category C] {D : Type (u₂+1)} [large_category D]

def ess_surj_of_equivalence (F : C ⥤ D) [is_equivalence F] : ess_surj F :=
⟨ λ Y : D, F.inv Y, λ Y : D, (nat_iso.app F.inv_fun_id Y) ⟩

instance faithful_of_equivalence (F : C ⥤ D) [is_equivalence F] : faithful F :=
{ injectivity' := λ X Y f g w, begin
                                have p := congr_arg (@category_theory.functor.map _ _ _ _ F.inv _ _) w,
                                simp at *,
                                assumption
                              end }.

instance full_of_equivalence (F : C ⥤ D) [is_equivalence F] : full F :=
{ preimage := λ X Y f, (nat_iso.app F.fun_inv_id X).inv ≫ (F.inv.map f) ≫ (nat_iso.app F.fun_inv_id Y).hom,
  witness' := λ X Y f,
    begin
      apply F.inv.injectivity,
      obviously,
    end }.

section

private def equivalence_inverse (F : C ⥤ D) [full F] [faithful F] [ess_surj F] : D ⥤ C :=
{ obj  := λ X, F.obj_preimage X,
  map' := λ X Y f, F.preimage ((F.fun_obj_preimage_iso X).hom ≫ f ≫ (F.fun_obj_preimage_iso Y).inv),
  map_id' := λ X, begin apply F.injectivity, obviously, end,
  map_comp' := λ X Y Z f g, begin apply F.injectivity, obviously, end }.

-- FIXME pure boilerplate...
@[simp] private lemma equivalence_inverse_map
  (F : C ⥤ D) [full F] [faithful : faithful F] [ess_surj F]
  {X Y : D} (f : X ⟶ Y) : (equivalence_inverse F).map f = F.preimage ((F.fun_obj_preimage_iso X).hom ≫ f ≫ (F.fun_obj_preimage_iso Y).inv) := rfl.

def equivalence_of_fully_faithfully_ess_surj
  (F : C ⥤ D) [full F] [faithful : faithful F] [ess_surj F] : is_equivalence F :=
{ inverse := equivalence_inverse F,
  fun_inv_id' := nat_iso.of_components
    (λ X, preimage_iso (F.fun_obj_preimage_iso (F X)))
    (λ X Y f, begin apply F.injectivity, obviously, end),
  inv_fun_id' := nat_iso.of_components
    (λ Y, (F.fun_obj_preimage_iso Y))
    (by obviously) }
end

end category_theory.equivalence