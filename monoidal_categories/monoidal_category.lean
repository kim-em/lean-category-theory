-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .tensor_product

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation

namespace tqft.categories.monoidal_category

structure {u v} MonoidalStructure ( C : Category.{u v} ) :=
  (tensor                    : TensorProduct C)
  (tensor_unit               : C.Obj)
  (associator_transformation : Associator tensor)
  (left_unitor               : LeftUnitor tensor_unit tensor)
  (right_unitor              : RightUnitor tensor_unit tensor)

  (pentagon                  : Pentagon associator_transformation)
  (triangle                  : Triangle tensor_unit left_unitor right_unitor associator_transformation)

attribute [ematch] MonoidalStructure.pentagon
attribute [simp,ematch] MonoidalStructure.triangle

instance MonoidalStructure_coercion_to_TensorProduct { C : Category } : has_coe (MonoidalStructure C) (TensorProduct C) :=
  { coe := MonoidalStructure.tensor }

-- Convenience methods which take two arguments, rather than a pair. (This seems to often help the elaborator avoid getting stuck on `prod.mk`.)
@[reducible] definition MonoidalStructure.tensorObjects { C : Category } ( m : MonoidalStructure C ) ( X Y : C.Obj ) : C.Obj := m ⟨X, Y⟩
@[reducible] definition MonoidalStructure.tensorMorphisms { C : Category } ( m : MonoidalStructure C ) { W X Y Z : C.Obj } ( f : C.Hom W X ) ( g : C.Hom Y Z ) : C.Hom (m ⟨W, Y⟩) (m ⟨X, Z⟩) := m.tensor.onMorphisms ⟨f, g⟩

@[reducible] definition MonoidalStructure.associator
  { C : Category }
  ( m : MonoidalStructure C )
  ( X Y Z : C.Obj ) : C.Hom (m.tensorObjects (m.tensorObjects X Y) Z) (m.tensorObjects X (m.tensorObjects Y Z)) :=
  m.associator_transformation ⟨⟨X, Y⟩, Z⟩

@[reducible] definition MonoidalStructure.inverse_associator
  { C : Category }
  ( m : MonoidalStructure C )
  ( X Y Z : C.Obj ) : C.Hom (m.tensorObjects X (m.tensorObjects Y Z)) (m.tensorObjects (m.tensorObjects X Y) Z) :=
  m.associator_transformation.inverse.components ⟨⟨X, Y⟩, Z⟩

-- @[ematch] lemma MonoidalStructure.triangle_components { C : Category } ( m : MonoidalStructure C ) ( X Y : C.Obj ) :
--   C.compose (m.associator X m.tensor_unit Y) (m.tensorMorphisms (C.identity X) (m.left_unitor Y)) = m.tensorMorphisms (m.right_unitor X) (C.identity Y) := 
--   begin
--     exact m.triangle X Y,
--   end

-- @[ematch] lemma MonoidalStructure.triangle_components_inverse { C : Category } ( m : MonoidalStructure C ) ( X Y : C.Obj ) :
--   C.compose (m.inverse_associator X m.tensor_unit Y) (m.tensorMorphisms (m.right_unitor X) (C.identity Y)) = m.tensorMorphisms (C.identity X) (m.left_unitor Y) := 
--   begin
--     erewrite - m.triangle_components X Y,
--     erewrite - C.associativity,
--     dsimp,
--     erewrite m.associator_transformation.componentwise_witness_2 ((X, m.tensor_unit), Y),
--     simp,
--     trivial
--   end

-- TODO This works, but why do we need to be so explicit??
@[ematch] definition MonoidalStructure.interchange
  { C : Category }
  ( m : MonoidalStructure C )
  { U V W X Y Z: C.Obj }
  ( f : C.Hom U V )( g : C.Hom V W )( h : C.Hom X Y )( k : C.Hom Y Z ) :
  @Functor.onMorphisms _ _ m.tensor ⟨U, X⟩ ⟨W, Z⟩ ⟨(C.compose f g), (C.compose h k)⟩
  = C.compose
      (@Functor.onMorphisms _ _ m.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨f, h⟩)
      (@Functor.onMorphisms _ _ m.tensor ⟨V, Y⟩ ⟨W, Z⟩ ⟨g, k⟩) :=
  @Functor.functoriality (C × C) C m.tensor ⟨U, X⟩ ⟨V, Y⟩ ⟨W, Z⟩ ⟨f, h⟩ ⟨g, k⟩

@[ematch] lemma MonoidalStructure.interchange_left_identity
  { C : Category }
  ( m : MonoidalStructure C )
  { W X Y Z : C.Obj }
  ( f : C.Hom W X ) ( g : C.Hom X Y ) :
  @Functor.onMorphisms _ _ m.tensor ⟨W, Z⟩ ⟨Y, Z⟩ ⟨C.compose f g, C.identity Z⟩
    = C.compose (@Functor.onMorphisms _ _ m.tensor (W, Z) (X, Z) (f, C.identity Z)) (@Functor.onMorphisms _ _ m.tensor (X, Z) (Y, Z) (g, C.identity Z)) := ♯

@[ematch] lemma MonoidalStructure.interchange_right_identity
  { C : Category }
  ( m : MonoidalStructure C )
  { W X Y Z : C.Obj }
  ( f : C.Hom W X ) ( g : C.Hom X Y ) :
  @Functor.onMorphisms _ _ m.tensor ⟨Z, W⟩ ⟨Z, Y⟩ ⟨C.identity Z, C.compose f g⟩
    = C.compose (@Functor.onMorphisms _ _ m.tensor (Z, W) (Z, X) (C.identity Z, f)) (@Functor.onMorphisms _ _ m.tensor (Z, X) (Z, Y) (C.identity Z, g)) := ♯

@[ematch] lemma MonoidalStructure.interchange_identities
  { C : Category }
  ( m : MonoidalStructure C )
  { W X Y Z : C.Obj }
  ( f : C.Hom W X ) ( g : C.Hom Y Z ) :
  C.compose (m.tensorMorphisms (C.identity Y) f) (m.tensorMorphisms g (C.identity X))
    = C.compose (m.tensorMorphisms g (C.identity W)) (m.tensorMorphisms (C.identity Z) f) :=
    begin
     dsimp, dunfold MonoidalStructure.tensorMorphisms,
     rewrite - MonoidalStructure.interchange,
     simp,
     rewrite - MonoidalStructure.interchange,
     simp
    end

@[simp,ematch] lemma MonoidalStructure.tensor_identities
  { C : Category }
  ( m : MonoidalStructure C )
  ( X Y : C.Obj ) :
   @Functor.onMorphisms _ _ (m.tensor) (X, Y) (X, Y) (C.identity X, C.identity Y) = C.identity (m.tensor.onObjects (X, Y)) := ♮

-- lemma MonoidalStructure.associator_naturality_0
--   { C : Category }
--   ( m : MonoidalStructure C )
--   { U V W X Y Z : C.Obj }
--   (f : C U V ) ( g : C W X ) ( h : C Y Z ) :
--     C.compose
--       (m.tensorMorphisms (m.tensorMorphisms f g) h)
--       (m.associator_transformation ((V, X), Z))
--     = C.compose
--       (m.associator_transformation ((U, W), Y))
--       (m.tensorMorphisms f (m.tensorMorphisms g h)) := 
--   begin
--     dsimp,
--     apply @NaturalTransformation.naturality _ _ _ _ m.associator_transformation ((U, W), Y) ((V, X), Z) ((f, g), h)
--   end

lemma MonoidalStructure.inverse_associator_naturality_0
  { C : Category }
  ( m : MonoidalStructure C )
  { U V W X Y Z : C.Obj }
  (f : C.Hom U V ) ( g : C.Hom W X ) ( h : C.Hom Y Z ) :
    C.compose
      (@Functor.onMorphisms _ _ m.tensor (U, _) (V, _) (f, (@Functor.onMorphisms _ _ m.tensor (W, _) (X, _) (g, h))))
      (((m.associator_transformation).inverse).components ((V, X), Z))
    = C.compose
      (((m.associator_transformation).inverse).components ((U, W), Y))
      (@Functor.onMorphisms _ _ m.tensor (_, Y) (_, Z) ((@Functor.onMorphisms _ _ m.tensor (U, _) (V, _) (f, g)), h)) :=
  begin
    dsimp,
    apply @NaturalTransformation.naturality _ _ _ _ ((m.associator_transformation).inverse) ((U, W), Y) ((V, X), Z) ((f, g), h)
  end

-- lemma MonoidalStructure.associator_naturality
--   { C : Category }
--   ( m : MonoidalStructure C )
--   { U V W X Y Z : C.Obj }
--   (f : C U V ) ( g : C W X ) ( h : C Y Z ) :
--     C.compose
--       (m.tensorMorphisms (m.tensorMorphisms f g) h)
--       (m.associator V X Z)
--     = C.compose
--       (m.associator U W Y)
--       (m.tensorMorphisms f (m.tensorMorphisms g h)) := 
--   begin
--     dsimp,
--     apply @NaturalTransformation.naturality _ _ _ _ m.associator_transformation ((U, W), Y) ((V, X), Z) ((f, g), h)
--   end

-- lemma MonoidalStructure.inverse_associator_naturality
--   { C : Category }
--   ( m : MonoidalStructure C )
--   { U V W X Y Z : C.Obj }
--   (f : C U V ) ( g : C W X ) ( h : C Y Z ) :
--     C.compose
--       (m.tensorMorphisms f (m.tensorMorphisms g h))
--       (m.inverse_associator V X Z)
--     = C.compose
--       (m.inverse_associator U W Y)
--       (m.tensorMorphisms (m.tensorMorphisms f g) h) := 
--   begin
--     dsimp,
--     apply @NaturalTransformation.naturality _ _ _ _ ((m.associator_is_isomorphism).inverse) ((U, W), Y) ((V, X), Z) ((f, g), h)
--   end

@[simp] lemma TensorProduct.two_identities
  { C : Category }
  ( m : MonoidalStructure C )
  ( X Y : C.Obj ) : @Functor.onMorphisms _ _ m.tensor ⟨X, Y⟩ ⟨X, Y⟩ ⟨C.identity X, C.identity Y⟩ = C.identity (m.tensor.onObjects ⟨X, Y⟩) := ♮

-- set_option old_structure_cmd true

structure {u v} MonoidalCategory extends C : Category.{u v} :=
  ( m : MonoidalStructure C )

definition {u v} MonoidalCategory_coercion_to_Category : has_coe MonoidalCategory.{u v} Category.{u v} :=
  { coe := MonoidalCategory.C }

attribute [instance] MonoidalCategory_coercion_to_Category


-- PROJECT If multiple coercions were allowed, and field access could use coercions, then we might try:
-- structure MonoidalCategory :=
--   ( C : Category )
--   ( m : MonoidalStructure C )

-- instance MonoidalCategory_coercion_to_MonoidalStructure : has_coe_to_fun (MonoidalCategory) :=
-- { F   := λ m, MonoidalStructure m.C,
--   coe := MonoidalCategory.m }
-- instance MonoidalCategory_coercion_to_Category : has_coe MonoidalCategory Category :=
--   { coe := MonoidalCategory.C }

-- def f ( C : MonoidalCategory ) := Category.identity C
-- def g ( C : MonoidalCategory ) := MonoidalStructure.tensor_unit C

end tqft.categories.monoidal_category
