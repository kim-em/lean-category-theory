-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category
open tqft.categories.isomorphism

namespace tqft.categories.monoidal_functor

universe variables u1 v1 u2 v2 u3 v3

structure MonoidalFunctor { C : Category.{u1 v1} } ( m : MonoidalStructure C ) { D : Category.{u2 v2} } ( n : MonoidalStructure D ) :=
  ( functor : Functor C D )
  ( tensorator : NaturalIsomorphism (FunctorComposition m.tensor functor) (FunctorComposition (functor × functor) n.tensor) )
  ( associativity : ∀ X Y Z : C.Obj, 
      D.compose (tensorator (m (X, Y), Z)) (D.compose (n.tensorMorphisms (tensorator (X, Y)) (D.identity (functor Z))) (n.associator (functor X) (functor Y) (functor Z)))
      = D.compose (functor.onMorphisms (m.associator X Y Z)) (D.compose (tensorator (X, m (Y, Z))) (n.tensorMorphisms (D.identity (functor X)) (tensorator (Y, Z))))
  )
  ( identerator : Isomorphism D (functor m.tensor_unit) n.tensor_unit)
  ( left_identity  : ∀ X : C.Obj, D.compose (tensorator (m.tensor_unit, X)) (D.compose (n.tensorMorphisms identerator.morphism (D.identity (functor X))) (n.left_unitor  (functor X))) = functor.onMorphisms (m.left_unitor X)  )
  ( right_identity : ∀ X : C.Obj, D.compose (tensorator (X, m.tensor_unit)) (D.compose (n.tensorMorphisms (D.identity (functor X)) identerator.morphism) (n.right_unitor (functor X))) = functor.onMorphisms (m.right_unitor X) )
  
attribute [simp,ematch] MonoidalFunctor.left_identity
attribute [simp,ematch] MonoidalFunctor.right_identity
attribute [ematch]      MonoidalFunctor.associativity

instance MonoidalFunctor_coercion_to_functor { C : Category.{u1 v1} } ( m : MonoidalStructure C ) { D : Category.{u2 v2} } ( n : MonoidalStructure D ) : has_coe (MonoidalFunctor m n) (Functor C D) :=
  { coe := MonoidalFunctor.functor }

-- PROJECT composition of MonoidalFunctors

-- PROJECT Automation should construct even the tensorator! Perhaps we need to mark certain transformations and isomorphisms as allowed.

-- open tactic
-- open interactive
-- meta def precompose { C : Category } { X Y : C.Obj } ( f : C X Y ) : tactic unit := refine { exact (C.compose f _) }

-- definition MonoidalFunctorComposition
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { E : Category.{u3 v3} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   { o : MonoidalStructure E }
--   ( F : MonoidalFunctor m n ) ( G : MonoidalFunctor n o ) : MonoidalFunctor m o :=
-- {
--   functor        := @FunctorComposition C D E F G,
--   tensorator     := {
--     morphism  := begin                   
--                    rewrite - FunctorComposition.associativity,
--                    exact sorry
--                  end,
--     inverse   := sorry,
--     witness_1 := sorry,
--     witness_2 := sorry
--   },
--   associativity  := sorry,
--   identerator    := sorry,
--   left_identity  := sorry,
--   right_identity := sorry
-- }

structure MonoidalNaturalTransformation
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { m : MonoidalStructure C }
  { n : MonoidalStructure D }
  ( F G : MonoidalFunctor m n ) :=
  ( natural_transformation : NaturalTransformation F.functor G.functor )
  ( compatibility_with_tensor : ∀ X Y : C.Obj, D.compose (F.tensorator (X, Y)) (n.tensorMorphisms (natural_transformation X) (natural_transformation Y)) = D.compose (natural_transformation (m.tensorObjects X Y)) (G.tensorator (X, Y)) )
  ( compatibility_with_unit   : D.compose (natural_transformation m.tensor_unit) G.identerator.morphism = F.identerator.morphism )

attribute [simp,ematch] MonoidalNaturalTransformation.compatibility_with_tensor
attribute [simp,ematch] MonoidalNaturalTransformation.compatibility_with_unit

-- @[pointwise] lemma MonoidalNaturalTransformation_componentwise_equal
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   ( F G : MonoidalFunctor m n )
--   ( α β : MonoidalNaturalTransformation F G )
--   ( w : α.natural_transformation = β.natural_transformation ) : α = β :=
--   begin
--     induction α with α_components α_naturality,
--     induction β with β_components β_naturality,
--     dsimp at w,
--     -- blast
--   end

-- instance MonoidalNaturalTransformation_coercion_to_NaturalTransformation
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   ( F G : MonoidalFunctor m n ) : has_coe (MonoidalNaturalTransformation F G) (NaturalTransformation F.functor G.functor) :=
--   { coe := MonoidalNaturalTransformation.natural_transformation }

-- definition IdentityMonoidalNaturalTransformation
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   ( F : MonoidalFunctor m n ) : MonoidalNaturalTransformation F F :=
--     ⟨ IdentityNaturalTransformation F.functor, ♮, ♮ ⟩

-- definition vertical_composition_of_MonoidalNaturalTransformations
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D }
--   { F G H : MonoidalFunctor m n } 
--   ( α : MonoidalNaturalTransformation F G ) 
--   ( β : MonoidalNaturalTransformation G H ) : MonoidalNaturalTransformation F H :=
-- {
--   natural_transformation    := vertical_composition_of_NaturalTransformations α.natural_transformation β.natural_transformation,
--   compatibility_with_tensor := begin
--                                 -- abstract {
--                                   -- TODO It seems that one round of blast should succeed here!
--                                   -- blast,
--                                   intros, dsimp,
--                                   rewrite D.interchange,
--                                   rewrite - D.associativity,
--                                   rewrite α.compatibility_with_tensor,
--                                   -- blast, -- This blast seems to cause the CPU to pin at maximum, and start ignoring earlier edits.
--                                   rewrite D.associativity,
--                                   rewrite β.compatibility_with_tensor,
--                                   blast -- What is this blast even doing? It seems dsimp should be enough.
--                                 -- }
--                                end,
--   compatibility_with_unit   := ♮                               
-- }

-- PROJECT horizontal_composition_of_MonoidalNaturalTransformations
-- definition horizontal_composition_of_MonoidalNaturalTransformations
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { E : Category.{u3 v3} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure C }
--   { o : MonoidalStructure C }
--   { F G : MonoidalFunctor m n } 
--   { H K : MonoidalFunctor n o } 
--   ( α : MonoidalNaturalTransformation F G ) 
--   ( β : MonoidalNaturalTransformation H K ) : MonoidalNaturalTransformation (MonoidalFunctorComposition F H) (MonoidalFunctorComposition G K) :=
-- {
--   natural_transformation    := horizontal_composition_of_NaturalTransformations α.natural_transformation β.natural_transformation,
--   compatibility_with_tensor := sorry,
--   compatibility_with_unit   := sorry
-- }


-- definition CategoryOfMonoidalFunctors   
--   { C : Category.{u1 v1} }
--   { D : Category.{u2 v2} }
--   { m : MonoidalStructure C }
--   { n : MonoidalStructure D } : Category :=
-- {
--   Obj := MonoidalFunctor C D,
--   Hom := MonoidalNaturalTransformation,
--   identity := IdentityMonoidalNaturalTransformation,
--   compose  := λ _ _ _ α β, vertical_composition_of_MonoidalNaturalTransformations α β,

--   left_identity  := ♮,
--   right_identity := ♮,
--   associativity  := ♮
-- }

end tqft.categories.monoidal_functor