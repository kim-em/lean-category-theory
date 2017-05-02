-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category
import .isomorphism

open tqft.categories
open tqft.categories.isomorphism

namespace tqft.categories.functor

structure {u1 v1 u2 v2} Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C.Obj → D.Obj)
  (onMorphisms : Π { X Y : C.Obj },
                C.Hom X Y → D.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C.Obj),
    onMorphisms (C.identity X) = D.identity (onObjects X))
  (functoriality : ∀ { X Y Z : C.Obj } (f : C.Hom X Y) (g : C.Hom Y Z),
    onMorphisms (C.compose f g) = D.compose (onMorphisms f) (onMorphisms g))

attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality
attribute [pointwise] Functor.mk

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C.Obj → D.Obj,
  coe := Functor.onObjects }

-- This defines a coercion allowing us to write `F f` for `onMorphisms F f`
-- but sadly it doesn't work if to_onObjects is already in scope.
-- instance Functor_to_onMorphisms { C D : Category } : has_coe_to_fun (Functor C D) :=
-- { F   := λ f, Π ⦃X Y : C.Obj⦄, C.Hom X Y → D.Hom (f X) (f Y), -- contrary to usual use, `f` here denotes the Functor.
--  coe := Functor.onMorphisms }

definition {u1 v1} IdentityFunctor ( C: Category.{u1 v1} ) : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f,
  identities    := ♮,
  functoriality := ♮
}

definition {u1 v1 u2 v2 u3 v3} FunctorComposition { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} } ( F : Functor C D ) ( G : Functor D E ) : Functor C E :=
{
  onObjects     := λ X, G.onObjects (F.onObjects X),
  onMorphisms   := λ _ _ f, G.onMorphisms (F.onMorphisms f),
  identities    := ♯,
  functoriality := ♮
}

-- We'll want to be able to prove that two functors are equal if they are equal on objects and on morphisms.
-- Implementation warning:
-- When using `apply Functors_pointwise_equal`, you might expect that Lean will create two goals,
--   one for `objectWitness`, and one for `morphismWitness`.
--   However, because `morphismWitness` depends on `objectWitness`, it will actually only create the goal
--   for `morphismWitness`, leaving the `objectWitness` goal somehow "implicit" and likely unprovable.
--   See https://groups.google.com/d/msg/lean-user/bhStu87PjiI/vqsyr9ZABAAJ for details.
-- If you run into this problem, use `fapply Functors_pointwise_equal` instead.
@[pointwise] lemma {u1 v1 u2 v2} Functors_pointwise_equal
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} } 
  { F G : Functor C D } 
  ( objectWitness : ∀ X : C.Obj, F.onObjects X = G.onObjects X ) 
  ( morphismWitness : ∀ X Y : C.Obj, ∀ f : C.Hom X Y, ⟦ F.onMorphisms f ⟧ = G.onMorphisms f ) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  assert h_objects : F_onObjects = G_onObjects, exact funext objectWitness,
  subst h_objects,
  assert h_morphisms : @F_onMorphisms = @G_onMorphisms, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  exact morphismWitness X Y f,
  subst h_morphisms
end

-- Functors preserve isomorphisms
definition {u1 v1 u2 v2} Functor_onIsomorphisms
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} } 
  {X Y : C.Obj}
  (F : Functor C D)
  (g : Isomorphism C X Y) :
  Isomorphism D (F.onObjects X) (F.onObjects Y) :=
  {
    morphism := F.onMorphisms g.morphism,
    inverse := F.onMorphisms g.inverse,
    witness_1 := ♮,
    witness_2 := ♮
  }

end tqft.categories.functor
