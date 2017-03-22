-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.products
open tqft.categories.monoidal_category

namespace tqft.categories.strict_monoidal_category

structure TensorProduct_is_strict { C : Category } ( tensor : TensorProduct C ) ( tensor_unit : C^.Obj ) :=
  ( associativeOnObjects  : ∀ X Y Z : C^.Obj, tensor^.onObjects (tensor^.onObjects (X, Y), Z) = tensor^.onObjects (X, tensor^.onObjects (Y, Z)) )
  ( strictLeftTensorUnit  : ∀ X : C^.Obj, tensor^.onObjects (tensor_unit, X) = X )
  ( strictRightTensorUnit : ∀ X : C^.Obj, tensor^.onObjects (X, tensor_unit) = X )

attribute [ematch] TensorProduct_is_strict.associativeOnObjects
-- TODO why is this not a valid simplification lemma?
-- attribute [simp,ematch] TensorProduct_is_strict.strictLeftTensorUnit
-- attribute [simp,ematch] TensorProduct_is_strict.strictRightTensorUnit

-- definition construct_StrictMonoidalCategory { C : Category } { tensor : TensorProduct C } { tensor_unit : C^.Obj } ( is_strict : TensorProduct_is_strict tensor tensor_unit ) : MonoidalCategory :=
-- {
--   Obj := C^.Obj,
--   Hom := λ X Y : C^.Obj, C^.Hom X Y,
--   compose := λ _ _ _ f g, C^.compose f g,
--   identity := λ X, C^.identity X,
--   left_identity := λ _ _ f, C^.left_identity f,
--   right_identity := λ _ _ f, C^.right_identity f,
--   associativity := λ _ _ _ _ f g h, C^.associativity f g h,
--   tensor := {
--     onObjects     := λ p, tensor^.onObjects p,
--     onMorphisms   := λ _ _ f, tensor^.onMorphisms f,
--     identities    := ♮,
--     functoriality := ♮
--   },
--   tensor_unit := tensor_unit,
--   associator_transformation := {
--     components := λ t, begin
--                         -- TODO Really we want to be able to just write `exact ...` at the beginning, and be left with
--                         --  goals to show that really was the right type of thing, which can be automated.
--                            blast,
--                            dsimp [ProductCategory] at t,
--                            rewrite - is_strict^.associativeOnObjects,
--                            assert p : ((t^.fst)^.fst, (t^.fst)^.snd) = t^.fst, blast,
--                            rewrite p,
--                            exact C^.identity (tensor^.onObjects (tensor^.onObjects t^.fst, t^.snd))                           
--                        end,
--     naturality := sorry -- TODO Given how we constructed components, I have no idea how to prove naturality.
--   },
--   left_unitor := sorry,
--   right_unitor := sorry,
--   associator_is_isomorphism := sorry,
--   left_unitor_is_isomorphism := sorry,
--   right_unitor_is_isomorphism := sorry,
--   pentagon := sorry,
--   triangle := sorry
-- }  

@[reducible] definition tensorList { C : MonoidalCategory } ( X : list C^.Obj ) : C^.Obj := list.foldl C^.tensorObjects C^.tensor_unit X

-- @[reducible] definition tensorListConcatenation { C : MonoidalCategory } ( X : list C^.Obj × list C^.Obj ) : Isomorphism C (C^.tensorObjects (tensorList X.1) (tensorList X.2)) (tensorList (append X.1 X.2)) :=
-- {
--   morphism  := sorry,
--   inverse   := sorry,
--   witness_1 := sorry,
--   witness_2 := sorry
-- }

-- @[reducible] definition ListObjectsCategory ( C : MonoidalCategory ) : Category := {
--   Obj := list C^.Obj,
--   Hom := λ X Y, C^.Hom (tensorList X) (tensorList Y),
--   identity       := λ X, C^.identity (tensorList X),
--   compose        := λ _ _ _ f g, C^.compose f g,
--   left_identity  := ♮,
--   right_identity := ♮,
--   associativity  := sorry
-- }

-- definition StrictTensorProduct ( C : MonoidalCategory ) : TensorProduct (ListObjectsCategory C) := {
--   onObjects     := λ X, append X.1 X.2,
--   onMorphisms   := λ X Y f, sorry, -- C^.compose (C^.compose (tensorListConcatenation X)^.inverse f) (tensorListConcatenation Y)^.morphism,
--   identities    := sorry,
--   functoriality := sorry
-- }

-- PROJECT
-- * show that StrictTensorProduct is strict
-- * construct a functor from C
-- * show that it is part of an equivalence

end tqft.categories.strict_monoidal_category
