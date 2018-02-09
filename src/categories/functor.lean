-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category
import .isomorphism

open categories
open categories.isomorphism

namespace categories.functor

universes u1 v1 u2 v2 u3 v3

variable (C : Type u1)
variable (D : Type u2)
variable (E : Type u3)

structure Functor [category.{u1 v1} C] [category.{u2 v2} D] :=
  (onObjects   : C → D)
  (onMorphisms : Π {X Y : C},
                Hom X Y → Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C),
    onMorphisms (𝟙 X) = 𝟙 (onObjects X) . tidy')
  (functoriality : ∀ {X Y Z : C} (f : Hom X Y) (g : Hom Y Z),
    onMorphisms (f >> g) = (onMorphisms f) >> (onMorphisms g) . tidy')

make_lemma Functor.identities
make_lemma Functor.functoriality
attribute [simp,ematch] Functor.identities_lemma
attribute [simp,ematch] Functor.functoriality_lemma

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects [category.{u1 v1} C] [category.{u2 v2} D]: has_coe_to_fun (Functor C D) :=
{F   := λ f, C → D,
  coe := Functor.onObjects}

definition IdentityFunctor [category.{u1 v1} C] : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f
}

definition FunctorComposition {C : Category.{u1 v1}} {D : Category.{u2 v2}} {E : Category.{u3 v3}} (F : Functor C D) (G : Functor D E) : Functor C E :=
{
  onObjects     := λ X, G.onObjects (F.onObjects X),
  onMorphisms   := λ _ _ f, G.onMorphisms (F.onMorphisms f)
}

-- Functors preserve isomorphisms
definition {u1 v1 u2 v2} Functor_onIsomorphisms
  {C : Category.{u1 v1}}
  {D : Category.{u2 v2}} 
  {X Y : C.Obj}
  (F : Functor C D)
  (g : Isomorphism C X Y) :
  Isomorphism D (F.onObjects X) (F.onObjects Y) :=
  {
    morphism := F.onMorphisms g.morphism,
    inverse := F.onMorphisms g.inverse
 }

class ReflectsIsomorphisms {C D : Category} (F : Functor C D) :=
  (reflects : Π {X Y : C.Obj} (f : C.Hom X Y) (w : is_Isomorphism (F.onMorphisms f)), is_Isomorphism f)

end categories.functor
