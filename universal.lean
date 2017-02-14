-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .category
import .functor
import .natural_transformation

open tqft.categories

namespace tqft.categories.universal

structure InitialObject ( C : Category ) :=
  (object : C^.Obj)
  (morphism : ∀ Y : C^.Obj, C^.Hom object Y)
  (uniqueness :  ∀ Y : C^.Obj, ∀ f : C^.Hom object Y, f = morphism Y)

structure TerminalObject ( C : Category ) :=
  (object : C^.Obj)
  (morphism : ∀ Y : C^.Obj, C^.Hom Y object)
  (uniqueness :  ∀ Y : C^.Obj, ∀ f : C^.Hom Y object, f = morphism Y)

-- TODO define a coercion along `object`

structure is_initial { C : Category } ( X : C^.Obj ) :=
  (morphism : ∀ Y : C^.Obj, C^.Hom X Y)
  (uniqueness :  ∀ Y : C^.Obj, ∀ f : C^.Hom X Y, f = morphism Y)
  

lemma InitialObjects_are_unique { C : Category } ( X Y : InitialObject C ) : Isomorphism C X^.object Y^.object :=
  {
      morphism := X^.morphism Y^.object,
      inverse := Y^.morphism X^.object,
      witness_1 := begin exact sorry end,
      witness_2 := sorry
  }

open tqft.categories.functor
open tqft.categories.natural_transformation

-- The diagonal functor sends X to the constant functor that sends everything to X.
definition DiagonalFunctor ( J C : Category ) : Functor C (FunctorCategory J C) :=
{
  onObjects     := λ X: C^.Obj, {
    onObjects     := λ _, X,
    onMorphisms   := λ _ _ _, C^.identity X,
    identities    := ♮,
    functoriality := ♮
  },
  onMorphisms   := λ X Y f, {
    components := λ _, f,
    naturality := ♮
  },
  identities    := ♮,
  functoriality := ♮  
}

-- The elaborator has some trouble understanding what p.2.2 and q.2.2 mean below.
-- Leo suggested the following work-around, at <https://groups.google.com/d/msg/lean-user/8jW4BIUFl24/MOtgbpfqCAAJ>.
local attribute [elab_simple]  sigma.snd

-- TODO can one automatically coerce along subtype.elt_of?
open subtype

definition CommaCategory { A B C : Category} ( S : Functor A C ) ( T : Functor B C ) : Category :=
{
  Obj      := Σ a : A^.Obj, Σ b : B^.Obj, C^.Hom (S a) (T b),
  Hom      := λ p q, { gh : (A^.Hom p.1 q.1) × (B^.Hom p.2.1 q.2.1) // C^.compose (S^.onMorphisms gh.1) q.2.2 = C^.compose p.2.2 (T^.onMorphisms gh.2) },
  identity := λ p, tag (A^.identity p.1, B^.identity p.2.1) ♮,
  compose  := λ p q r f g, tag (A^.compose (elt_of f).1 (elt_of g).1, B^.compose (elt_of f).2 (elt_of g).2)
                 begin
                   abstract compose_tag {
                     blast,
                     rewrite C^.associativity,
                     rewrite g^.has_property,
                     rewrite - C^.associativity,
                     rewrite - C^.associativity,
                     rewrite - f^.has_property
                   }
                 end,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := begin blast, rewrite [ A^.associativity, B^.associativity ] end
}

def One: Category :=
{
  Obj      := unit,
  Hom      := λ _ _, unit,
  identity := λ _, unit.star,
  compose  := λ _ _ _ _ _, unit.star,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

definition ObjectAsFunctor { C : Category } ( X : C^.Obj ) : Functor One C :=
{
  onObjects     := λ _, X,
  onMorphisms   := λ _ _ _, C^.identity X,
  identities    := ♮,
  functoriality := ♮
}

-- TODO probably better to give the simplified definition of slice and coslice categories, and then prove equivalence with this.
definition SliceCategory   { C : Category } ( X : C^.Obj ) := CommaCategory (IdentityFunctor C) (ObjectAsFunctor X) 
definition CosliceCategory { C : Category } ( X : C^.Obj ) := CommaCategory (ObjectAsFunctor X) (IdentityFunctor C)

definition Cones   { J C : Category } ( F : Functor J C ) := CommaCategory (DiagonalFunctor J C) (ObjectAsFunctor F)
definition Cocones { J C : Category } ( F : Functor J C ) := CommaCategory (@ObjectAsFunctor (FunctorCategory J C) F) (DiagonalFunctor J C)

-- TODO is this definition actually usable??
definition Limit   { J C : Category } ( F: Functor J C ) := TerminalObject (Cones F)
definition Colimit { J C : Category } ( F: Functor J C ) := InitialObject (Cocones F)

-- TODO then equalizers, etc.

-- TODO ... how to handle dual notions without too much duplication?

end tqft.categories.universal

