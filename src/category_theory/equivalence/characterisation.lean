-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.equivalence
import category_theory.natural_isomorphism
import tidy.rewrite_search

import tidy.command.rfl_lemma

open category_theory

namespace category_theory.equivalence

universes u₁ u₂

variables {C : Type (u₁+1)} [large_category C] {D : Type (u₂+1)} [large_category D]

def ess_surj_of_equivalence (F : C ⥤ D) [is_equivalence F] : ess_surj F :=
⟨ λ Y : D, F.inv.obj Y, λ Y : D, (nat_iso.app F.inv_fun_id Y) ⟩

instance faithful_of_equivalence (F : C ⥤ D) [is_equivalence F] : faithful F :=
{ injectivity' := λ X Y f g w, begin
                                have p := congr_arg (@category_theory.functor.map _ _ _ _ F.inv _ _) w,
                                simp at *,
                                assumption
                              end }.

open tidy.rewrite_search.tracer
open tidy.rewrite_search.strategy
open tidy.rewrite_search.metric

instance full_of_equivalence (F : C ⥤ D) [is_equivalence F] : full F :=
{ preimage := λ X Y f, (nat_iso.app F.fun_inv_id X).inv ≫ (F.inv.map f) ≫ (nat_iso.app F.fun_inv_id Y).hom,
  witness' := λ X Y f,
    begin
      apply F.inv.injectivity,
      tidy,
      rewrite_search_using [`search] { --view := visualiser,
                                       trace_summary := tt,
                                       strategy := pexplore {pop_size := 3},
                                       },
    end }.

section

@[simp] private def equivalence_inverse (F : C ⥤ D) [full F] [faithful F] [ess_surj F] : D ⥤ C :=
{ obj  := λ X, F.obj_preimage X,
  map := λ X Y f, F.preimage ((F.fun_obj_preimage_iso X).hom ≫ f ≫ (F.fun_obj_preimage_iso Y).inv),
  map_id' := λ X, begin apply F.injectivity, obviously, end,
  map_comp' := λ X Y Z f g, begin apply F.injectivity, obviously, end }.

def equivalence_of_fully_faithfully_ess_surj
  (F : C ⥤ D) [full F] [faithful : faithful F] [ess_surj F] : is_equivalence F :=
{ inverse := equivalence_inverse F,
  fun_inv_id' := nat_iso.of_components
    (λ X, preimage_iso (F.fun_obj_preimage_iso (F.obj X)))
    (λ X Y f, begin apply F.injectivity, obviously, end),
  inv_fun_id' := nat_iso.of_components
    (λ Y, (F.fun_obj_preimage_iso Y))
    (by obviously) }
end

end category_theory.equivalence