-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category_0

--set_option pp.universes true

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
  -- TODO left and right identitors
  (pentagon                  : Pentagon associator_transformation)
  -- TODO triangles for the identitors

instance LaxMonoidalCategory_coercion : has_coe LaxMonoidalCategory.{u v} Category.{u v} :=
  ⟨LaxMonoidalCategory.to_Category⟩

structure MonoidalCategory
  extends LaxMonoidalCategory :=
  (associator_is_isomorphism : is_NaturalIsomorphism associator_transformation)

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
@[reducible] definition MonoidalCategory.tensorObjects   ( C : MonoidalCategory ) ( X Y : C^.Obj ) : C^.Obj := C^.tensor (X, Y)
@[reducible] definition MonoidalCategory.tensorMorphisms ( C : MonoidalCategory ) { W X Y Z : C^.Obj } ( f : C^.Hom W X ) ( g : C^.Hom Y Z ) : C^.Hom (C^.tensor (W, Y)) (C^.tensor (X, Z)) := C^.tensor^.onMorphisms (f, g)

definition MonoidalCategory.associator
  ( C : MonoidalCategory )
  ( X Y Z : C^.Obj ) : C^.Hom (C^.tensorObjects (C^.tensorObjects X Y) Z) (C^.tensorObjects X (C^.tensorObjects Y Z)) :=
  C^.associator_transformation ((X, Y), Z)

instance MonoidalCategory_coercion_to_LaxMonoidalCategory   : has_coe MonoidalCategory.{u v} LaxMonoidalCategory.{u v}   := ⟨MonoidalCategory.to_LaxMonoidalCategory⟩

-- TODO This works, but do we really need to be so explicit??
@[reducible] definition MonoidalCategory.interchange
  ( C : MonoidalCategory )
  { U V W X Y Z: C^.Obj }
  ( f : C^.Hom U V )( g : C^.Hom V W )( h : C^.Hom X Y )( k : C^.Hom Y Z ) : 
  @Functor.onMorphisms _ _ C^.tensor (U, X) (W, Z) ((C^.compose f g), (C^.compose h k)) = C^.compose (@Functor.onMorphisms _ _ C^.tensor (U, X) (V, Y) (f, h)) (@Functor.onMorphisms _ _ C^.tensor (V, Y) (W, Z) (g, k)) :=
  @Functor.functoriality (C × C) C C^.tensor (U, X) (V, Y) (W, Z) (f, h) (g, k)

--namespace notations
--  infix `⊗`:70 := λ {C : MonoidalCategory} (X Y : C^.Obj),
--                    C^.tensorObjects X Y
--  infix `⊗`:70 := λ {C : MonoidalCategory} {W X Y Z : C^.Obj}
--                     (f : C^.Hom W X) (g : C^.Hom Y Z),
--                     C^.tensorMorphisms f g
--end notations

-- per https://groups.google.com/d/msg/lean-user/kkIFgWRJTLo/tr2VyJGmCQAJ
  
end tqft.categories.monoidal_category
