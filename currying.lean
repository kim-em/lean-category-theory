-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .equivalence
import .products.products

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor
open tqft.categories.equivalence

namespace tqft.categories.natural_transformation

-- PROJECT show Fun(C → Fun(D → E)) is equivalent to Fun(C × D → E)

@[simp] lemma {u v w} foo { α : Type u } { β : Type v } { Z : α × β → Type w } ( f : Π (a : α) (b : β),  Z (a, b) ) ( x : α ) ( y : β ): (@prod.rec α β Z (λ (a : α) (b : β), f a b) (x, y)) = f x y :=
begin
  simp
end
@[simp] lemma {u v w} bar { α : Type u } { β : Type v } { Z : α × β → Type w } ( f : Π (a : α) (b : β),  Z (a, b) ) ( x : α ) ( y : β ): (@prod.rec α β Z (λ (a : α), f a) (x, y)) = f x y :=
begin
  simp
end

-- set_option pp.all true

-- theorem {u1 v1 u2 v2 u3 v3} Currying_for_functors
--   ( C : Category.{u1 v1} )
--   ( D : Category.{u2 v2} )
--   ( E : Category.{u3 v3} ) :
theorem {u} Currying_for_functors
  ( C : Category.{u u} )
  ( D : Category.{u u} )
  ( E : Category.{u u} ) :
  Equivalence (FunctorCategory C (FunctorCategory D E)) (FunctorCategory (C × D) E) :=
--   begin
--     fsplit,
--     fsplit,
--     {      
--       -- Define the functor
--       unfold_projections,
--       intros F,
--       fsplit,
--       {
--         -- define it on objects
--         intros,
--         induction a with c d,
--         exact (F.onObjects c).onObjects d,
--       },
--       {
--         intros,
--         induction X with X_1 X_2,
--         induction Y with Y_1 Y_2,
--         induction a with f g,
--         simp at f,
--         simp at g,
--         pose p := (F.onMorphisms f),
--         unfold_projections at p,   
--         unfold_projections, -- FIXME we're stuck here on prod.rec
--         simp,
--         admit
--       }
--     }
--   end

  {
    functor := {
      onObjects     := λ F, {
        onObjects     := λ X, (F.onObjects X.1).onObjects X.2,
        onMorphisms   := λ X Y f, sorry,
        identities    := sorry,
        functoriality := sorry
      },
      onMorphisms   := λ F G T, {
        components := sorry,       -- PROJECT really we should only have to specify this; everything else is determined
        naturality := sorry
      },
      identities    := sorry,
      functoriality := sorry
    },
    inverse := sorry,
    isomorphism_1 := sorry,
    isomorphism_2 := sorry
  }

end tqft.categories.natural_transformation