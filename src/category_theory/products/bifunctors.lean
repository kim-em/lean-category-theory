-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .products

open categories
open categories.functor
open categories.natural_transformation

namespace categories.products

@[simp] lemma {u1 v1 u2 v2 u3 v3} Bifunctor_identities
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  ( F : Functor (C × D) E )
  ( X : C.Obj )
  ( Y : D.Obj )
  : @Functor.onMorphisms _ _ F (X, Y) (X, Y) (C.identity X, D.identity Y) = E.identity (F.onObjects (X, Y))
  := F.identities (X, Y)

@[simp] lemma {u1 v1 u2 v2 u3 v3} Bifunctor_left_identity
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  ( F : Functor (C × D) E )
  ( W : C.Obj )
  { X Y Z : D.Obj }
  ( f : D.Hom X Y )
  ( g : D.Hom Y Z )
  : @Functor.onMorphisms _ _ F (W, X) (W, Z) (C.identity W, D.compose f g) =
      E.compose (@Functor.onMorphisms _ _ F (W, X) (W, Y) (C.identity W, f)) (@Functor.onMorphisms _ _ F (W, Y) (W, Z) (C.identity W, g)) :=
begin
  have p := @Functor.functoriality _ _ F (W, X) (W, Y) (W, Z) (C.identity W, f) (C.identity W, g),
  tidy,
  exact p
end

@[simp] lemma {u1 v1 u2 v2 u3 v3} Bifunctor_right_identity
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  ( F : Functor (C × D) E )
  ( X Y Z : C.Obj )
  { W : D.Obj }
  ( f : C.Hom X Y )
  ( g : C.Hom Y Z )
  : @Functor.onMorphisms _ _ F (X, W) (Z, W) (C.compose f g, D.identity W) =
      E.compose (@Functor.onMorphisms _ _ F (X, W) (Y, W) (f, D.identity W)) (@Functor.onMorphisms _ _ F (Y, W) (Z, W) (g, D.identity W)) :=
begin
  have p := @Functor.functoriality _ _ F (X, W) (Y, W) (Z, W) (f, D.identity W) (g, D.identity W),
  tidy,
  exact p
end

@[simp] lemma {u1 v1 u2 v2 u3 v3} Bifunctor_diagonal_identities_1
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  ( F : Functor (C × D) E )
  ( X X' : C.Obj )
  ( f : C.Hom X X' )
  ( Y Y' : D.Obj )
  ( g : D.Hom Y Y' )
  : E.compose (@Functor.onMorphisms _ _ F (X, Y) (X, Y') (C.identity X, g)) (@Functor.onMorphisms _ _ F (X, Y') (X', Y') (f, D.identity Y')) =
   @Functor.onMorphisms _ _ F (X, Y) (X', Y') (f, g) :=
begin
  have p := eq.symm (@Functor.functoriality _ _ F (X, Y) (X, Y') (X', Y') (C.identity X, g) (f, D.identity Y')),
  tidy,
  exact p
end

@[simp] lemma {u1 v1 u2 v2 u3 v3} Bifunctor_diagonal_identities_2
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { E : Category.{u3 v3} }
  ( F : Functor (C × D) E )
  ( X X' : C.Obj )
  ( f : C.Hom X X' )
  ( Y Y' : D.Obj )
  ( g : D.Hom Y Y' )
  : E.compose (@Functor.onMorphisms _ _ F (X, Y) (X', Y) (f, D.identity Y)) (@Functor.onMorphisms _ _ F (X', Y) (X', Y') (C.identity X', g)) =
   @Functor.onMorphisms _ _ F (X, Y) (X', Y') (f, g) :=
begin
  have p := eq.symm (@Functor.functoriality _ _ F (X, Y) (X', Y) (X', Y') (f, D.identity Y) (C.identity X', g)),
  tidy,
  exact p
end

end categories.products
