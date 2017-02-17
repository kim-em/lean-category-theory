-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..products

--set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

universe variables u v

@[reducible] definition TensorProduct ( C: Category ) := Functor ( C × C ) C

structure PreMonoidalCategory
  -- this is only for internal use: it has a tensor product, but no associator at all
  -- it's not interesting mathematically, but may allow us to introduce usable notation for the tensor product
  extends carrier : Category :=
  (tensor : TensorProduct carrier)
  (tensor_unit : Obj)

instance PreMonoidalCategory_coercion : has_coe PreMonoidalCategory Category := 
  ⟨PreMonoidalCategory.to_Category⟩

definition left_associated_triple_tensor ( C : PreMonoidalCategory ) : Functor ((C × C) × C) C :=
  FunctorComposition (C^.tensor × IdentityFunctor C) C^.tensor
definition right_associated_triple_tensor ( C : PreMonoidalCategory ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × C^.tensor) C^.tensor

definition Associator ( C : PreMonoidalCategory ) := 
  NaturalTransformation 
    (left_associated_triple_tensor C) 
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor C))

/-
definition associator_to_components { C : PreMonoidalCategory } ( α : Associator C ) : associator_components C := 
begin
 induction α,
 -- TODO how do we even begin here?
 -- I just want to change the goal from producing an instance of `associator_components C` to producing the function that actually represents
 exact sorry
end
-/

/- 
-- In general one can't construct an associator from components, because we need proofs of naturality.
-- One should thus build a tactic, something like `blast_naturality components`
-- which look at the components and then attempts to use automation to construct the proof of naturality. 
-/

definition left_associated_quadruple_tensor ( C : PreMonoidalCategory ) :
  Functor (((C × C) × C) × C) C :=
  FunctorComposition
    (FunctorComposition
      ((C^.tensor × IdentityFunctor C) × IdentityFunctor C)
      (C^.tensor × IdentityFunctor C))
    C^.tensor

definition right_associated_quadruple_tensor ( C : PreMonoidalCategory ) :
  Functor (C × (C × (C × C))) C :=
  FunctorComposition
    (FunctorComposition
      (IdentityFunctor C × (IdentityFunctor C  × C^.tensor))
      (IdentityFunctor C × C^.tensor))
    C^.tensor

definition pentagon_3step_1 { C : PreMonoidalCategory } ( α : Associator C ) :=
  whisker_on_right
    (α × IdentityNaturalTransformation (IdentityFunctor C))
    C^.tensor

definition pentagon_3step_2 { C : PreMonoidalCategory } ( α : Associator C ) :=
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      ((IdentityFunctor C × C^.tensor) × IdentityFunctor C))
    α

definition pentagon_3step_3 { C : PreMonoidalCategory } ( α : Associator C ) :=
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator C C C × IdentityFunctor C)
      (ProductCategoryAssociator C (↑C × ↑C) C))
    (whisker_on_right
      (IdentityNaturalTransformation (IdentityFunctor C) × α)
      C^.tensor)

definition pentagon_3step { C : PreMonoidalCategory } ( α : Associator C ) :=
  vertical_composition_of_NaturalTransformations
    (vertical_composition_of_NaturalTransformations
      (pentagon_3step_1 α)
      (pentagon_3step_2 α))
    (pentagon_3step_3 α)

definition pentagon_2step_1 { C : PreMonoidalCategory } ( α : Associator C ) :=
  whisker_on_left
    ((C^.tensor × IdentityFunctor C) × IdentityFunctor C)
    α

definition pentagon_2step_2 { C : PreMonoidalCategory } ( α : Associator C ) :=
  whisker_on_left
    (FunctorComposition
      (ProductCategoryAssociator (↑C × ↑C) C C)
      (IdentityFunctor (↑C × ↑C) × C^.tensor))
    α

definition pentagon_2step { C : PreMonoidalCategory } ( α : Associator C ) :=
  vertical_composition_of_NaturalTransformations
    (pentagon_2step_1 α)
    (pentagon_2step_2 α)

structure LaxMonoidalCategory
  extends carrier : PreMonoidalCategory :=
  (associator : Associator carrier)
  (pentagon   : pentagon_3step associator = pentagon_2step associator)

/-
-- TODO (far future)
-- One should prove the first substantial result of this theory: that any two ways to reparenthesize are equal.
-- It requires introducing a representation of a reparenthesization, but the proof should then be an easy induction.
-- It's a good example of something that is so easy for humans, that it better eventually be easy for the computer too!
-/

-- Notice that LaxMonoidalCategory.tensor has a horrible signature...
-- It sure would be nice if it read ... Functor (carrier × carrier) carrier
-- print LaxMonoidalCategory

instance LaxMonoidalCategory_coercion : has_coe LaxMonoidalCategory PreMonoidalCategory :=
  ⟨LaxMonoidalCategory.to_PreMonoidalCategory⟩

structure OplaxMonoidalCategory
  extends carrier : PreMonoidalCategory :=
  -- TODO better name? unfortunately it doesn't yet make sense to say 'inverse_associator'.
  (backwards_associator : Π (X Y Z : Obj),
     Hom (tensor (X, tensor (Y, Z)))  (tensor (tensor (X, Y), Z)))

instance OplaxMonoidalCategory_coercion : has_coe OplaxMonoidalCategory PreMonoidalCategory :=
  ⟨OplaxMonoidalCategory.to_PreMonoidalCategory⟩

structure MonoidalCategory
  extends LaxMonoidalCategory, OplaxMonoidalCategory :=
  (associators_inverses_1: Π (X Y Z : Obj), compose (associator X Y Z) (backwards_associator X Y Z) = identity (tensor (tensor (X, Y), Z)))
  (associators_inverses_2: Π (X Y Z : Obj), compose (backwards_associator X Y Z) (associator X Y Z) = identity (tensor (X, tensor (Y, Z))))

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
@[reducible] definition MonoidalCategory.tensorObjects ( C : MonoidalCategory ) ( X Y : C^.Obj ) : C^.Obj := C^.tensor (X, Y)
@[reducible] definition MonoidalCategory.tensorMorphisms ( C : MonoidalCategory ) { W X Y Z : C^.Obj } ( f : C^.Hom W X ) ( g : C^.Hom Y Z ) : C^.Hom (C^.tensor (W, Y)) (C^.tensor (X, Z)) := C^.tensor^.onMorphisms (f, g)

instance MonoidalCategory_coercion_to_LaxMonoidalCategory : has_coe MonoidalCategory LaxMonoidalCategory := ⟨MonoidalCategory.to_LaxMonoidalCategory⟩
instance MonoidalCategory_coercion_to_OplaxMonoidalCategory : has_coe MonoidalCategory OplaxMonoidalCategory := ⟨MonoidalCategory.to_OplaxMonoidalCategory⟩

-- TODO This works, but do we really need to be so explicit??
@[reducible] definition MonoidalCategory.interchange
  ( C : MonoidalCategory )
  { U V W X Y Z: C^.Obj }
  ( f : C^.Hom U V )( g : C^.Hom V W )( h : C^.Hom X Y )( k : C^.Hom Y Z ) : 
  @Functor.onMorphisms _ _ C^.tensor (U, X) (W, Z) ((C^.compose f g), (C^.compose h k)) = C^.compose (@Functor.onMorphisms _ _ C^.tensor (U, X) (V, Y) (f, h)) (@Functor.onMorphisms _ _ C^.tensor (V, Y) (W, Z) (g, k)) :=
  @Functor.functoriality (C × C) C C^.tensor (U, X) (V, Y) (W, Z) (f, h) (g, k)

namespace notations
  infix `⊗`:70 := λ {C : MonoidalCategory} (X Y : C^.Obj),
                    C^.tensorObjects X Y
  infix `⊗`:70 := λ {C : MonoidalCategory} {W X Y Z : C^.Obj}
                     (f : C^.Hom W X) (g : C^.Hom Y Z),
                     C^.tensorMorphisms f g
end notations

-- per https://groups.google.com/d/msg/lean-user/kkIFgWRJTLo/tr2VyJGmCQAJ
local attribute [reducible] lift_t coe_t coe_b

definition tensor_on_left { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects Z X,
  onMorphisms := λ X Y f, C^.tensorMorphisms (C^.identity Z) f,
  identities := begin
                  blast,
                  rewrite Functor.identities (C^.tensor),                
                end,
  functoriality := begin
                      blast,
                      -- TODO, why doesn't this work?
                      -- begin[smt]
                      --   eblast_using [ Category.left_identity, MonoidalCategory.interchange ]
                      -- end,
                      rewrite - C^.interchange,
                      rewrite C^.left_identity
                    end
}

definition tensor_on_right { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects X Z,
  onMorphisms := λ X Y f, C^.tensorMorphisms f (C^.identity Z),
  identities := begin
                  blast,
                  rewrite Functor.identities (C^.tensor),                
                end,
  functoriality := begin
                      blast,
                      rewrite - C^.interchange,
                      rewrite C^.left_identity
                    end
}
  
end tqft.categories.monoidal_category
