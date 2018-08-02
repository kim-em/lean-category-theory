-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.products.bifunctors
import categories.equivalence

open categories
open categories.equivalence
open categories.products
open categories.functor

namespace categories.currying

universes u₁ u₂ v₂ 

variables (C : Type u₁) [small_category C] (D : Type u₁) [small_category D] (E : Type u₂) [ℰ : category.{u₂ v₂} E]
include ℰ

#print Functor.identities_lemma




-- The 'obviously' fields here are only here for studying rewrite_search.
definition Uncurry_Functors : (C ↝ (D ↝ E)) ↝ ((C × D) ↝ E) := 
{ onObjects     := λ F, { onObjects     := λ X, (F +> X.1) +> X.2,
                          onMorphisms   := λ X Y f, ((F &> f.1) X.2) ≫ ((F +> Y.1) &> f.2),
                          functoriality := sorry, identities := begin intros,
cases X,
dsimp at *,
simp at *,
-- rewrite_search_using `ematch {trace:=tt,trace_rules:=tt},
perform_nth_rewrite [ProductCategory.identity] 0,
rw ProductCategory.identity,
rw Functor.identities_lemma,
refl
 end },
  onMorphisms   := λ F G T, { components := λ X, (T X.1) X.2,
                              naturality := sorry -- begin intros, cases f, cases Y, cases X, dsimp at *, simp at *, rewrite_search_using `ematch {trace:=tt, trace_result:=tt} end 
                              } }

definition Curry_Functors : ((C × D) ↝ E) ↝ (C ↝ (D ↝ E)) := 
{ onObjects     := λ F, { onObjects     := λ X, { onObjects     := λ Y, F +> (X, Y),
                                                  onMorphisms   := λ Y Y' g, F &> (𝟙 X, g) },
                          onMorphisms   := λ X X' f, { components := λ Y, F.onMorphisms (f, 𝟙 Y) } },
  onMorphisms   := λ F G T, { components := λ X, { components := λ Y, T.components (X, Y) } } }

local attribute [applicable] category.identity -- this is usually a bad idea, but just what we needed here
local attribute [tidy] dsimp_all'

def Currying_for_functors : Equivalence (C ↝ (D ↝ E)) ((C × D) ↝ E) := 
{ functor := Uncurry_Functors C D E,
  inverse := Curry_Functors C D E }

end categories.currying