-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_categories.monoidal_category

namespace tqft.categories.enriched

open tqft.categories.monoidal_category

structure EnrichedCategory (V: MonoidalCategory) :=
  (Obj : Type )
  (Hom : Obj → Obj → V^.Obj)
  (compose :  Π { X Y Z : Obj }, V^.Hom (V^.tensorObjects (Hom X Y) (Hom Y Z)) (Hom X Z))
  (identity : Π X : Obj, V^.Hom V^.tensor_unit (Hom X X))
  (left_identity  : ∀ { X Y : Obj }, 
    V^.compose 
      (V^.left_unitor_is_isomorphism^.inverse (Hom X Y)) 
    (V^.compose 
      (V^.tensorMorphisms (identity X) (V^.identity (Hom X Y))) 
      compose
    ) = V^.identity (Hom X Y) )
  (right_identity  : ∀ { X Y : Obj }, 
    V^.compose 
      (V^.right_unitor_is_isomorphism^.inverse (Hom X Y)) 
    (V^.compose 
      (V^.tensorMorphisms (V^.identity (Hom X Y)) (identity Y)) 
      compose
    ) = V^.identity (Hom X Y) )
  (associativity : ∀ { W X Y Z : Obj },
    V^.compose 
      (V^.tensorMorphisms compose (V^.identity (Hom Y Z))) 
      compose
   = V^.compose 
      (V^.associator (Hom W X) (Hom X Y) (Hom Y Z)) 
    (V^.compose 
      (V^.tensorMorphisms (V^.identity (Hom W X)) compose)
      compose) )

attribute [simp,ematch] EnrichedCategory.left_identity
attribute [simp,ematch] EnrichedCategory.right_identity
attribute [ematch] EnrichedCategory.associativity

instance EnrichedCategory_to_Hom { V : MonoidalCategory } : has_coe_to_fun (EnrichedCategory V) :=
{ F   := λ C, C^.Obj → C^.Obj → V^.Obj,
  coe := EnrichedCategory.Hom }

structure Functor { V : MonoidalCategory } ( C D : EnrichedCategory V ) :=
  ( onObjects : C^.Obj → D^.Obj )
  ( onMorphisms : ∀ { X Y : C^.Obj }, V^.Hom (C X Y) (D (onObjects X) (onObjects Y)) )
  ( identities : ∀ X : C^.Obj, V^.compose (C^.identity X) onMorphisms = D^.identity (onObjects X) )
  ( functoriality : ∀ { X Y Z : C^.Obj }, V^.compose C^.compose (@onMorphisms X Z) = V^.compose (V^.tensorMorphisms (@onMorphisms X Y) (@onMorphisms Y Z)) D^.compose )

attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality

  -- PROJECT natural transformations don't always exist; you need various limits!
  -- PROJECT products for categories enriched in symmetric categories
  -- PROJECT 2-categories as categories enriched in categories
  -- PROJECT strict n-categories

end tqft.categories.enriched