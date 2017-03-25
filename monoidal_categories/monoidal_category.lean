-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .tensor_product

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

structure LaxMonoidalCategory
  extends carrier : Category :=
  (tensor                    : TensorProduct carrier)
  (tensor_unit               : Obj)
  (associator_transformation : Associator tensor)
  (left_unitor               : LeftUnitor ⟦tensor_unit⟧ tensor)
  (right_unitor              : RightUnitor ⟦tensor_unit⟧ tensor)

  (pentagon                  : Pentagon associator_transformation)
  (triangle                  : Triangle ⟦tensor_unit⟧ left_unitor right_unitor associator_transformation)

attribute [ematch] LaxMonoidalCategory.pentagon

-- TODO Unfortunately we need to copy these attributes; this isn't handled by inheritance.
attribute [ematch,simp] LaxMonoidalCategory.left_identity
attribute [ematch,simp] LaxMonoidalCategory.right_identity
attribute [ematch] LaxMonoidalCategory.associativity

instance LaxMonoidalCategory_coercion : has_coe LaxMonoidalCategory.{u v} Category.{u v} :=
  ⟨LaxMonoidalCategory.to_Category⟩

structure MonoidalCategory
  extends LaxMonoidalCategory :=
  (associator_is_isomorphism   : is_NaturalIsomorphism associator_transformation)
  (left_unitor_is_isomorphism  : is_NaturalIsomorphism left_unitor)
  (right_unitor_is_isomorphism : is_NaturalIsomorphism right_unitor)

-- TODO Unfortunately we need to copy these attributes; this isn't handled by inheritance.
attribute [ematch,simp] MonoidalCategory.left_identity
attribute [ematch,simp] MonoidalCategory.right_identity
attribute [ematch] MonoidalCategory.associativity
attribute [ematch] MonoidalCategory.pentagon

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
@[reducible] definition MonoidalCategory.tensorObjects   ( C : MonoidalCategory ) ( X Y : C^.Obj ) : C^.Obj := C^.tensor ⟨X, Y⟩
@[reducible] definition MonoidalCategory.tensorMorphisms ( C : MonoidalCategory ) { W X Y Z : C^.Obj } ( f : C^.Hom W X ) ( g : C^.Hom Y Z ) : C^.Hom (C^.tensor ⟨W, Y⟩) (C^.tensor ⟨X, Z⟩) := C^.tensor^.onMorphisms ⟨f, g⟩

@[reducible] definition MonoidalCategory.associator
  ( C : MonoidalCategory )
  ( X Y Z : C^.Obj ) : C^.Hom (C^.tensorObjects (C^.tensorObjects X Y) Z) (C^.tensorObjects X (C^.tensorObjects Y Z)) :=
  C^.associator_transformation ⟨⟨X, Y⟩, Z⟩
@[reducible] definition MonoidalCategory.inverse_associator
  ( C : MonoidalCategory )
  ( X Y Z : C^.Obj ) : C^.Hom (C^.tensorObjects X (C^.tensorObjects Y Z)) (C^.tensorObjects (C^.tensorObjects X Y) Z) :=
  C^.associator_is_isomorphism^.inverse ⟨⟨X, Y⟩, Z⟩

instance MonoidalCategory_coercion_to_LaxMonoidalCategory   : has_coe MonoidalCategory.{u v} LaxMonoidalCategory.{u v}   := ⟨MonoidalCategory.to_LaxMonoidalCategory⟩

-- TODO This works, but why do we need to be so explicit??
@[ematch] definition MonoidalCategory.interchange
  ( C : MonoidalCategory )
  { U V W X Y Z: C^.Obj }
  ( f : C^.Hom U V )( g : C^.Hom V W )( h : C^.Hom X Y )( k : C^.Hom Y Z ) :
  @Functor.onMorphisms _ _ C^.tensor ⟨U, X⟩ ⟨W, Z⟩ ⟨(C^.compose f g), (C^.compose h k)⟩
  = C^.compose
      (@Functor.onMorphisms _ _ C^.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨f, h⟩)
      (@Functor.onMorphisms _ _ C^.tensor ⟨V, Y⟩ ⟨W, Z⟩ ⟨g, k⟩) :=
  @Functor.functoriality (C × C) C C^.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨W, Z⟩ ⟨f, h⟩ ⟨g, k⟩

-- TODO it seems a shame we need to redine this for MonoidalCategory; it's already there on Category.
lemma MonoidalCategory.identity_idempotent
  ( C : MonoidalCategory )
  ( X : C^.Obj ) : C^.identity X = C^.compose (C^.identity X) (C^.identity X) := ♮

lemma MonoidalCategory.interchange_left_identity
  ( C : MonoidalCategory )
  { W X Y Z : C^.Obj }
  ( f : C^.Hom W X ) ( g : C^.Hom X Y ) :
  @Functor.onMorphisms _ _ C^.tensor ⟨W, Z⟩ ⟨Y, Z⟩ ⟨C^.compose f g, C^.identity Z⟩
    = C^.compose (C^.tensorMorphisms f (C^.identity Z)) (C^.tensorMorphisms g (C^.identity Z)) := ♮

lemma MonoidalCategory.interchange_right_identity
  ( C : MonoidalCategory )
  { W X Y Z : C^.Obj }
  ( f : C^.Hom W X ) ( g : C^.Hom X Y ) :
  @Functor.onMorphisms _ _ C^.tensor ⟨Z, W⟩ ⟨Z, Y⟩ ⟨C^.identity Z, C^.compose f g⟩
    = C^.compose (C^.tensorMorphisms (C^.identity Z) f) (C^.tensorMorphisms (C^.identity Z) g) := ♮

@[ematch] lemma MonoidalCategory.interchange_identities
  ( C : MonoidalCategory )
  { W X Y Z : C^.Obj }
  ( f : C^.Hom W X ) ( g : C^.Hom Y Z ) :
  C^.compose (C^.tensorMorphisms (C^.identity Y) f) (C^.tensorMorphisms g (C^.identity X))
    = C^.compose (C^.tensorMorphisms g (C^.identity W)) (C^.tensorMorphisms (C^.identity Z) f) := ♮

-- This is just C^.tensor^.identities, but because of inheritance issues it is sometimes hard to apply directly.
lemma TensorProduct_identities
  { C : MonoidalCategory }
  ( X Y : C^.Obj ) :
  C^.tensorMorphisms (C^.identity X) (C^.identity Y) = C^.identity (C^.tensorObjects X Y) := ♮

#print NaturalTransformation.naturality

section

local attribute [semireducible] left_associated_triple_tensor right_associated_triple_tensor

lemma MonoidalCategory.inverse_associator_naturality
  { C : MonoidalCategory }
  { U V W X Y Z : C^.Obj }
  (f : C U V ) ( g : C W X ) ( h : C Y Z ) :
    C^.compose
      (C^.inverse_associator U W Y)
      (@Functor.onMorphisms _ _ (left_associated_triple_tensor C^.tensor) ((U, W), Y) ((V, X), Z) ((f, g), h))
    = C^.compose
      (@Functor.onMorphisms _ _ (right_associated_triple_tensor C^.tensor) (U, (W, Y)) (V, (X, Z)) (f, (g, h))) 
      (C^.inverse_associator V X Z) :=
  begin
    dsimp,
    pose p := @NaturalTransformation.naturality _ _ _ _ ((C^.associator_is_isomorphism)^.inverse) ((U, W), Y) ((V, X), Z) ((f, g), h),
    simp at p,
  end

end

lemma MonoidalCategory.inverse_associator_naturality'
  { C : MonoidalCategory }
  { U V W X Y Z : C^.Obj }
  (f : C U V ) ( g : C W X ) ( h : C Y Z ) :
    C^.compose
      (C^.inverse_associator U W Y)
      (C^.tensorMorphisms (C^.tensorMorphisms f g) h)
    = C^.compose
      (C^.tensorMorphisms f (C^.tensorMorphisms g h))
      (C^.inverse_associator V X Z) := sorry

@[simp] lemma TensorProduct_two_identities
  { C : MonoidalCategory }
  ( X Y : C^.Obj ) : @Functor.onMorphisms _ _ C^.tensor ⟨X, Y⟩ ⟨X, Y⟩ ⟨C^.identity X, C^.identity Y⟩ = C^.identity (C^.tensor^.onObjects ⟨X, Y⟩) := ♮

end tqft.categories.monoidal_category
