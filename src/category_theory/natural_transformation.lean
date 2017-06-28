-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .isomorphism
import .functor

open categories
open categories.isomorphism
open categories.functor

namespace categories.natural_transformation

structure {u1 v1 u2 v2} NaturalTransformation { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F G : Functor C D ) :=
  (components: Π X : C.Obj, D.Hom (F.onObjects X) (G.onObjects X))
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
  ( w : ∀ X : C.Obj, α.components X = β.components X ) : α = β :=
  begin
    induction α with α_components α_naturality,
    induction β with β_components β_naturality,
    have hc : α_components = β_components := funext w,
    subst hc
  end

definition {u1 v1 u2 v2} IdentityNaturalTransformation { C : Category.{u1 v1} } { D : Category.{u2 v2} } (F : Functor C D) : NaturalTransformation F F :=
  {
    components := λ X, D.identity (F.onObjects X),
    naturality := ♮
  }

definition {u1 v1 u2 v2} vertical_composition_of_NaturalTransformations
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G H : Functor C D }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation G H ) : NaturalTransformation F H :=
  {
    components := λ X, D.compose (α.components X) (β.components X),
    naturality := ♮
  }

notation α `∘̬` β := vertical_composition_of_NaturalTransformations α β

open categories.functor

@[simp] lemma {u1 v1 u2 v2 u3 v3} FunctorComposition.onObjects { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  { F : Functor C D }
  { G : Functor D E }
  ( X : C.Obj ) : (FunctorComposition F G).onObjects X = G.onObjects (F.onObjects X) := begin blast end 

definition {u1 v1 u2 v2 u3 v3} horizontal_composition_of_NaturalTransformations
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  { F G : Functor C D }
  { H I : Functor D E }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation H I ) : NaturalTransformation (FunctorComposition F H) (FunctorComposition G I) :=
  {
    components := λ X : C.Obj, E.compose (β.components (F.onObjects X)) (I.onMorphisms (α.components X)),
    naturality := ♯
  }

-- FIXME Visual Studio Code can't seem to display the subscript h? ₕ
notation α `∘ᵤ` β := horizontal_composition_of_NaturalTransformations α β

definition {u1 v1 u2 v2 u3 v3} whisker_on_left
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  ( F : Functor C D )
  { G H : Functor D E }
  ( α : NaturalTransformation G H ) :
  NaturalTransformation (FunctorComposition F G) (FunctorComposition F H) :=
  horizontal_composition_of_NaturalTransformations (IdentityNaturalTransformation F) α

definition {u1 v1 u2 v2 u3 v3} whisker_on_right
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  { F G : Functor C D }
  ( α : NaturalTransformation F G )
  ( H : Functor D E ) :
  NaturalTransformation (FunctorComposition F H) (FunctorComposition G H) :=
  horizontal_composition_of_NaturalTransformations α (IdentityNaturalTransformation H)

-- To define a natural isomorphism, we'll define the functor category, and ask for an isomorphism there.
-- It's then a lemma that each component is an isomorphism, and vice versa.

definition {u1 v1 u2 v2} FunctorCategory ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) : Category :=
{
  Obj := Functor C D,
  Hom := λ F G, NaturalTransformation F G,

  identity := λ F, IdentityNaturalTransformation F,
  compose  := @vertical_composition_of_NaturalTransformations C D,

  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition {u1 v1 u2 v2 u3 v3} whisker_on_left_functor
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( E : Category.{u3 v3} )
  ( F : Functor C D ) :
  Functor (FunctorCategory D E) (FunctorCategory C E) :=
  {
    onObjects := λ G, FunctorComposition F G,
    onMorphisms := λ {G} {H} α, whisker_on_left F α,
    identities := ♯,
    functoriality := ♯
  }

definition {u1 v1 u2 v2 u3 v3} whisker_on_right_functor
  ( C : Category.{u1 v1} )
  { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  ( H : Functor D E ) :
  Functor (FunctorCategory C D) (FunctorCategory C E) :=
  {
    onObjects := λ F, FunctorComposition F H,
    onMorphisms := λ {F} {G} α, whisker_on_right α H,
    identities := ♯,
    functoriality := ♯
  }

@[reducible] definition {u1 v1 u2 v2} NaturalIsomorphism { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F G : Functor C D ) := Isomorphism (FunctorCategory C D) F G

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
   : D.compose (α.morphism.components X) (α.inverse.components X) = D.identity (F.onObjects X)
   := congr_arg (λ β, NaturalTransformation.components β X) α.witness_1
@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.componentwise_witness_2
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalIsomorphism F G )
  ( X : C.Obj )
   : D.compose (α.inverse.components X) (α.morphism.components X) = D.identity (G.onObjects X)
   := congr_arg (λ β, NaturalTransformation.components β X) α.witness_2

@[ematch] lemma {u1 v1 u2 v2} NaturalIsomorphism.naturality_1 
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalIsomorphism F G )
  { X Y : C.Obj }
  ( f : C.Hom X Y )
   : D.compose (D.compose (α.inverse.components X) (F.onMorphisms f)) (α.morphism.components Y) = G.onMorphisms f := 
   begin
     -- PROJECT automation
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
   : D.compose (D.compose (α.morphism.components X) (G.onMorphisms f)) (α.inverse.components Y) = F.onMorphisms f := 
   begin
     dsimp,
     rewrite - α.morphism.naturality,
     rewrite D.associativity,
     rewrite α.componentwise_witness_1,
     simp
   end

definition NaturalIsomorphism.from_components
  { C D : Category }
  { F G : Functor C D }
  ( components : ∀ X : C.Obj, Isomorphism D (F.onObjects X) (G.onObjects X) )
  ( naturality : ∀ { X Y : C.Obj } ( f : C.Hom X Y ), D.compose (F.onMorphisms f) (components Y).morphism = D.compose (components X).morphism (G.onMorphisms f) ) : NaturalIsomorphism F G :=
  {
    morphism  := {
      components := λ X, (components X).morphism,
      naturality := λ _ _ f, naturality f
    },
    inverse   := {
      components := λ X, (components X).inverse,
      naturality := λ X Y f, begin
                               let p := congr_arg (λ f : D.Hom (F.onObjects X) (G.onObjects Y), D.compose (components X).inverse (D.compose f (components Y).inverse)) (eq.symm (naturality f)),
                               simp at p,
                               rewrite D.associativity at p,
                               rewrite D.associativity at p,
                               rewrite Isomorphism.witness_1 at p,
                               rewrite - D.associativity at p,
                               rewrite D.right_identity at p,
                               rewrite Isomorphism.witness_2 at p,
                               rewrite D.left_identity at p,
                               exact p
                             end
    },
    witness_1 := ♯,
    witness_2 := ♯
  }

definition {u1 v1 u2 v2} vertical_composition_of_NaturalIsomorphisms 
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G H : Functor C D }
  ( α : NaturalIsomorphism F G )
  ( β : NaturalIsomorphism G H )
   : NaturalIsomorphism F H :=
  IsomorphismComposition α β

-- Newtype for isomorphisms in functor categories. This specialisation helps type inference.
structure {u1 v1 u2 v2} NaturalIsomorphism' {C : Category.{u1 v1}} {D : Category.{u2 v2}} (F G : Functor C D) :=
  mkNatIso :: (iso : Isomorphism (FunctorCategory C D) F G)

infix `≅ₙ`:50 := NaturalIsomorphism'

@[trans] definition {u1 v1 u2 v2} NaturalIsomorphismComposition
  { C : Category.{u1 v1} }
  { D : Category.{u2 v2} }
  { F G H : Functor C D }
  ( α : F ≅ₙ G ) ( β : G ≅ₙ H ) : F ≅ₙ H :=
  NaturalIsomorphism'.mkNatIso (vertical_composition_of_NaturalIsomorphisms α.iso β.iso)

open NaturalTransformation

definition {u1 v1 u2 v2} is_NaturalIsomorphism { C : Category.{u1 v1} } { D : Category.{u2 v2} }  { F G : Functor C D } ( α : NaturalTransformation F G ) := @is_Isomorphism (FunctorCategory C D) F G α

@[ematch] lemma {u1 v1 u2 v2} is_NaturalIsomorphism_componentwise_witness_1
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalTransformation F G )
  ( w : is_NaturalIsomorphism α )
  ( X : C.Obj )
   : D.compose (α.components X) (w.inverse.components X) = D.identity (F.onObjects X)
   := congr_arg (λ β, NaturalTransformation.components β X) w.witness_1
@[ematch] lemma {u1 v1 u2 v2} is_NaturalIsomorphism_componentwise_witness_2
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } 
  { F G : Functor C D }
  ( α : NaturalTransformation F G )
  ( w : is_NaturalIsomorphism α )
  ( X : C.Obj )
   : D.compose (w.inverse.components X) (α.components X) = D.identity (G.onObjects X)
   := congr_arg (λ β, NaturalTransformation.components β X) w.witness_2


lemma {u1 v1 u2 v2} IdentityNaturalTransformation_is_NaturalIsomorphism { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( F : Functor C D ) : is_NaturalIsomorphism (IdentityNaturalTransformation F) :=
  { inverse := IdentityNaturalTransformation F,
    witness_1 := ♯,
    witness_2 := ♯
  }

definition NaturalIsomorphism.components { C D : Category } { F G : Functor C D } ( α : NaturalIsomorphism F G ) ( X : C.Obj ) :
 Isomorphism D (F.onObjects X) (G.onObjects X) :=
  {
    morphism := α.morphism.components X,
    inverse := α.inverse.components X,
    witness_1 := ♮,
    witness_2 := ♮
  }

definition {u1 v1 u2 v2 u3 v3 u4 v4} FunctorComposition_associator
  { B : Category.{u1 v1} } { C : Category.{u2 v2} } { D : Category.{u3 v3} } { E : Category.{u4 v4} }
  ( F : Functor B C )
  ( G : Functor C D )
  ( H : Functor D E )
: NaturalIsomorphism (FunctorComposition (FunctorComposition F G) H) (FunctorComposition F (FunctorComposition G H)) := ♯

definition {u1 v1 u2 v2} FunctorComposition_left_unitor
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( F : Functor C D )
: NaturalIsomorphism (FunctorComposition (IdentityFunctor C) F) F := ♯

definition {u1 v1 u2 v2} FunctorComposition_right_unitor
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( F : Functor C D )
: NaturalIsomorphism (FunctorComposition F (IdentityFunctor D) ) F := ♯

end categories.natural_transformation
