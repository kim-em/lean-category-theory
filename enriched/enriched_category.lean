-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..monoidal_categories.monoidal_category

namespace tqft.categories.enriched

open tqft.categories
open tqft.categories.monoidal_category

structure {u v w} EnrichedCategory { V: Category.{v w} } ( m : MonoidalStructure V ) :=
  (Obj : Type u)
  (Hom : Obj → Obj → V.Obj)
  (compose :  Π { X Y Z : Obj }, V.Hom (m.tensorObjects (Hom X Y) (Hom Y Z)) (Hom X Z))
  (identity : Π X : Obj, V.Hom m.tensor_unit (Hom X X))
  (left_identity  : ∀ { X Y : Obj }, 
    V.compose 
      (m.left_unitor.inverse.components (Hom X Y)) -- TODO components
    (V.compose 
      (m.tensorMorphisms (identity X) (V.identity (Hom X Y))) 
      compose
    ) = V.identity (Hom X Y) )
  (right_identity  : ∀ { X Y : Obj }, 
    V.compose 
      (m.right_unitor.inverse.components (Hom X Y)) 
    (V.compose 
      (m.tensorMorphisms (V.identity (Hom X Y)) (identity Y)) 
      compose
    ) = V.identity (Hom X Y) )
  (associativity : ∀ { W X Y Z : Obj },
    V.compose 
      (m.tensorMorphisms compose (V.identity (Hom Y Z))) 
      compose
   = V.compose 
      (m.associator (Hom W X) (Hom X Y) (Hom Y Z)) 
    (V.compose 
      (m.tensorMorphisms (V.identity (Hom W X)) compose)
      compose) )

attribute [simp,ematch] EnrichedCategory.left_identity
attribute [simp,ematch] EnrichedCategory.right_identity
attribute [ematch] EnrichedCategory.associativity

instance EnrichedCategory_to_Hom { V : Category } { m : MonoidalStructure V } : has_coe_to_fun (EnrichedCategory m) :=
{ F   := λ C, C.Obj → C.Obj → V.Obj,
  coe := EnrichedCategory.Hom }

structure Functor { V : Category } { m : MonoidalStructure V } ( C D : EnrichedCategory m ) :=
  ( onObjects : C.Obj → D.Obj )
  ( onMorphisms : ∀ { X Y : C.Obj }, V.Hom (C X Y) (D (onObjects X) (onObjects Y)) )
  ( identities : ∀ X : C.Obj, V.compose (C.identity X) onMorphisms = D.identity (onObjects X) )
  ( functoriality : ∀ { X Y Z : C.Obj }, V.compose C.compose (@onMorphisms X Z) = V.compose (m.tensorMorphisms (@onMorphisms X Y) (@onMorphisms Y Z)) D.compose )

attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality

  -- PROJECT natural transformations don't always exist; you need various limits!
  
end tqft.categories.enriched