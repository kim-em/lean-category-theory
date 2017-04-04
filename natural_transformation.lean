-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .isomorphism
import .functor

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor

namespace tqft.categories.natural_transformation

structure {u1 v1 u2 v2} NaturalTransformation { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F G : Functor C D ) :=
  (components: Π X : C.Obj, D.Hom (F X) (G X))
  (naturality: ∀ { X Y : C.Obj } (f : C.Hom X Y),
     D.compose (F.onMorphisms f) (components Y) = D.compose (components X) (G.onMorphisms f))

attribute [ematch] NaturalTransformation.naturality

-- This defines a coercion so we can write `α X` for `components α X`.
instance NaturalTransformation_to_components { C D : Category } { F G : Functor C D } : has_coe_to_fun (NaturalTransformation F G) :=
{ F   := λ f, Π X : C.Obj, D.Hom (F X) (G X),
  coe := NaturalTransformation.components }

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
@[pointwise] lemma {u1 v1 u2 v2} NaturalTransformations_componentwise_equal
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α β : NaturalTransformation F G )
  ( w : ∀ X : C.Obj, α X = β X ) : α = β :=
  begin
    induction α with α_components α_naturality,
    induction β with β_components β_naturality,
    have hc : α_components = β_components, from funext w,
    by subst hc
  end

@[unfoldable] definition {u1 v1 u2 v2} IdentityNaturalTransformation { C : Category.{u1 v1} } { D : Category.{u2 v2} } (F : Functor C D) : NaturalTransformation F F :=
  {
    components := λ X, D.identity (F X),
    naturality := ♮
  }

@[unfoldable] definition {u1 v1 u2 v2} vertical_composition_of_NaturalTransformations
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G H : Functor C D }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation G H ) : NaturalTransformation F H :=
  {
    components := λ X, D.compose (α X) (β X),
    naturality := ♮
  }

open tqft.categories.functor

@[unfoldable] definition {u1 v1 u2 v2 u3 v3} horizontal_composition_of_NaturalTransformations
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  { F G : Functor C D }
  { H I : Functor D E }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation H I ) : NaturalTransformation (FunctorComposition F H) (FunctorComposition G I) :=
  {
    components := λ X : C.Obj, E.compose (β (F X)) (I.onMorphisms (α X)),
    naturality := ♯
  }

@[unfoldable] definition {u1 v1 u2 v2 u3 v3} whisker_on_left
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  ( F : Functor C D )
  { G H : Functor D E }
  ( α : NaturalTransformation G H ) :
  NaturalTransformation (FunctorComposition F G) (FunctorComposition F H) :=
  horizontal_composition_of_NaturalTransformations (IdentityNaturalTransformation F) α

@[unfoldable] definition {u1 v1 u2 v2 u3 v3} whisker_on_right
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  { F G : Functor C D }
  ( α : NaturalTransformation F G )
  ( H : Functor D E ) :
  NaturalTransformation (FunctorComposition F H) (FunctorComposition G H) :=
  horizontal_composition_of_NaturalTransformations α (IdentityNaturalTransformation H)

-- To define a natural isomorphism, we'll define the functor category, and ask for an isomorphism there.
-- It's then a lemma that each component is an isomorphism, and vice versa.

open tactic.interactive

@[unfoldable] definition {u1 v1 u2 v2} FunctorCategory ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) : Category :=
{
  Obj := Functor C D,
  Hom := λ F G, NaturalTransformation F G,

  identity := λ F, IdentityNaturalTransformation F,
  compose  := @vertical_composition_of_NaturalTransformations C D,

  left_identity  := by blast_as_simp FunctorCategory_left_identity,
  right_identity := by blast_as_simp FunctorCategory_right_identity,
  associativity  := by blast_as_simp FunctorCategory_associativity
}

definition {u1 v1 u2 v2} NaturalIsomorphism { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F G : Functor C D ) := Isomorphism (FunctorCategory C D) F G

-- It's a pity we need to separately define this coercion.
-- Ideally the coercion from Isomorphism along .morphism would just apply here.
-- Somehow we want the definition above to be more transparent?
instance NaturalIsomorphism_coercion_to_NaturalTransformation { C D : Category } ( F G : Functor C D ) : has_coe (NaturalIsomorphism F G) (NaturalTransformation F G) :=
  { coe := Isomorphism.morphism }

@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.componentwise_witness_1
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalIsomorphism F G )
  ( X : C.Obj )
   : D.compose (α.morphism.components X) (α.inverse.components X) = D.identity (F X)
   := congr_arg (λ β, NaturalTransformation.components β X) α.witness_1
@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.componentwise_witness_2
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalIsomorphism F G )
  ( X : C.Obj )
   : D.compose (α.inverse.components X) (α.morphism.components X) = D.identity (G X)
   := congr_arg (λ β, NaturalTransformation.components β X) α.witness_2

@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.naturality_1 
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalIsomorphism F G )
  { X Y : C.Obj }
  ( f : C.Hom X Y )
   : D^.compose (D^.compose (α.inverse.components X) (F.onMorphisms f)) (α.morphism.components Y) = G.onMorphisms f := 
   begin
    --  blast, -- FIXME ahh, I see; unfold_unfoldable is acting in the implicit arguments, making a mess.
     dsimp,
     rewrite - α.inverse.naturality,
     rewrite D.associativity,
     rewrite α.componentwise_witness_2,
     simp
   end
@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.naturality_2 
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalIsomorphism F G )
  { X Y : C.Obj }
  ( f : C.Hom X Y )
   : D^.compose (D^.compose (α.morphism.components X) (G.onMorphisms f)) (α.inverse.components Y) = F.onMorphisms f :=    begin
    --  blast, -- FIXME ahh, I see; unfold_unfoldable is acting in the implicit arguments, making a mess.
     dsimp,
     rewrite - α.morphism.naturality,
     rewrite D.associativity,
     rewrite α.componentwise_witness_1,
     simp
   end

-- definition NaturalIsomorphism.from_components
--   { C D : Category }
--   { F G : Functor C D }
--   ( components : ∀ X : C.Obj, Isomorphism D (F X) (G X) )
--   ( naturality : ∀ { X Y : C.Obj } ( f : C.Hom X Y ), D.compose (F.onMorphisms f) (components Y).morphism = D.compose (components X).morphism (G.onMorphisms f) ) : NaturalIsomorphism F G :=
--   {
--     morphism  := {
--       components := λ X, (components X).morphism,
--       naturality := λ _ _ f, naturality f
--     },
--     inverse   := {
--       components := λ X, (components X).inverse,
--       naturality := sorry
--     },
--     witness_1 := ♯,
--     witness_2 := ♯
  -- }

definition {u1 v1 u2 v2} vertical_composition_of_NaturalIsomorphisms 
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G H : Functor C D }
  ( α : NaturalIsomorphism F G )
  ( β : NaturalIsomorphism G H )
   : NaturalIsomorphism F H := {
  morphism := (FunctorCategory C D).compose α.morphism β.morphism,
  inverse  := (FunctorCategory C D).compose β.inverse  α.inverse,
  witness_1 := begin
                --  smt_eblast, -- FIXME why doesn't this work?                 
                 rewrite Category.associativity,
                 rewrite - (FunctorCategory C D).associativity β.morphism,
                 simp
               end,
  witness_2 := begin
                --  smt_eblast, -- FIXME why doesn't this work?
                 rewrite Category.associativity,
                 rewrite - (FunctorCategory C D).associativity α.inverse,
                 simp
               end
}

open NaturalTransformation

definition {u1 v1 u2 v2} is_NaturalIsomorphism { C : Category.{u1 v1} } { D : Category.{u2 v2} }  { F G : Functor C D } ( α : NaturalTransformation F G ) := @is_Isomorphism (FunctorCategory C D) F G α

@[ematch] lemma {u1 v1 u2 v2} is_NaturalIsomorphism_componentwise_witness_1
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalTransformation F G )
  ( w : is_NaturalIsomorphism α )
  ( X : C.Obj )
   : D.compose (α.components X) (w.inverse.components X) = D.identity (F X)
   := congr_arg (λ β, NaturalTransformation.components β X) w.witness_1
@[ematch] lemma {u1 v1 u2 v2} is_NaturalIsomorphism_componentwise_witness_2
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalTransformation F G )
  ( w : is_NaturalIsomorphism α )
  ( X : C.Obj )
   : D.compose (w.inverse.components X) (α.components X) = D.identity (G X)
   := congr_arg (λ β, NaturalTransformation.components β X) w.witness_2


lemma {u1 v1 u2 v2} IdentityNaturalTransformation_is_NaturalIsomorphism { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) : is_NaturalIsomorphism (IdentityNaturalTransformation F) :=
  { inverse := IdentityNaturalTransformation F,
    witness_1 := ♯,
    witness_2 := ♯
  }

lemma NaturalIsomorphism.components { C D : Category } { F G : Functor C D } ( α : NaturalIsomorphism F G ) ( X : C.Obj ) :
 Isomorphism D (F X) (G X) :=
  {
    morphism := α.morphism.components X,
    inverse := α.inverse.components X,
    witness_1 := ♮,
    witness_2 := ♮
  }

end tqft.categories.natural_transformation
