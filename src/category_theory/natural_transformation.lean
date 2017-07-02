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

notation α `∘ₕ` β := horizontal_composition_of_NaturalTransformations α β

definition {u1 v1 u2 v2 u3 v3} whisker_on_left
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  ( F : Functor C D )
  { G H : Functor D E }
  ( α : NaturalTransformation G H ) :
  NaturalTransformation (FunctorComposition F G) (FunctorComposition F H) :=
  (IdentityNaturalTransformation F) ∘ₕ α

definition {u1 v1 u2 v2 u3 v3} whisker_on_right
  { C : Category.{u1 v1} } { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  { F G : Functor C D }
  ( α : NaturalTransformation F G )
  ( H : Functor D E ) :
  NaturalTransformation (FunctorComposition F H) (FunctorComposition G H) :=
  α ∘ₕ (IdentityNaturalTransformation H)

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

definition {u1 v1 u2 v2 u3 v3} whiskering_on_left
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} ) :
    Functor (FunctorCategory C D) (FunctorCategory (FunctorCategory D E) (FunctorCategory C E)) :=
{
  onObjects     := λ F, {
    onObjects     := λ G, FunctorComposition F G,
    onMorphisms   := λ _ _ α, whisker_on_left F α,
    identities    := ♯,
    functoriality := ♯
  },
  onMorphisms   := λ F G τ, {
    components := λ H, {
      components := λ c, H.onMorphisms (τ.components c),
      naturality := ♯
    },
    naturality := ♯
  },
  identities    := ♯,
  functoriality := ♯
}

definition {u1 v1 u2 v2 u3 v3} whisker_on_left_functor
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( E : Category.{u3 v3} )
  ( F : Functor C D ) :
  Functor (FunctorCategory D E) (FunctorCategory C E) :=
  (whiskering_on_left C D E).onObjects F

definition {u1 v1 u2 v2 u3 v3} whiskering_on_right
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} ) :
    Functor (FunctorCategory D E) (FunctorCategory (FunctorCategory C D) (FunctorCategory C E)) :=
{
  onObjects     := λ H, {
    onObjects     := λ F, FunctorComposition F H,
    onMorphisms   := λ _ _ α, whisker_on_right α H,
    identities    := ♯,
    functoriality := ♯
  },
  onMorphisms   := λ G H τ, {
    components := λ F, {
      components := λ c, τ.components (F.onObjects c),
      naturality := ♯
    },
    naturality := ♯
  },
  identities    := ♯,
  functoriality := ♯
}


definition {u1 v1 u2 v2 u3 v3} whisker_on_right_functor
  ( C : Category.{u1 v1} )
  { D : Category.{u2 v2} } { E : Category.{u3 v3} }
  ( H : Functor D E ) :
  Functor (FunctorCategory C D) (FunctorCategory C E) :=
(whiskering_on_right C D E).onObjects H

end categories.natural_transformation
