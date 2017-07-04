-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..category

open categories
open categories.graphs

namespace categories.examples.graphs

@[pointwise] private lemma {u1 v1 u2 v2} GraphHomomorphisms_pointwise_equal
  { C : Graph.{u1 v1} }
  { D : Graph.{u2 v2} } 
  { F G : GraphHomomorphism C D } 
  ( objectWitness : ∀ X : C.Obj, F.onObjects X = G.onObjects X ) 
  ( morphismWitness : ∀ X Y : C.Obj, ∀ f : C.Hom X Y, ⟦ F.onMorphisms f ⟧ = G.onMorphisms f ) : F = G :=
begin
  induction F with F_onObjects F_onMorphisms,
  induction G with G_onObjects G_onMorphisms,
  have h_objects : F_onObjects = G_onObjects, exact funext objectWitness,
  subst h_objects,
  have h_morphisms : @F_onMorphisms = @G_onMorphisms, 
  apply funext, intro X, apply funext, intro Y, apply funext, intro f,
  exact morphismWitness X Y f,
  subst h_morphisms
end

definition CategoryOfGraphs : Category := {
    Obj := Graph,
    Hom := GraphHomomorphism,
    identity := λ G, {
        onObjects   := id,
        onMorphisms := λ _ _ f, f
    },
    compose := λ _ _ _ f g, {
        onObjects   := λ x, g.onObjects (f.onObjects x),
        onMorphisms := λ _ _ e, g.onMorphisms (f.onMorphisms e)
    },
    right_identity := ♯,
    left_identity  := ♯,
    associativity  := ♯
}

end categories.examples.graphs