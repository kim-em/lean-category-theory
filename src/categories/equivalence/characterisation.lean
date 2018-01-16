-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import ..equivalence

open categories
open categories.isomorphism
open categories.functor
open categories.natural_transformation

namespace categories.equivalence

lemma Equivalences_are_EssentiallySurjective { C D : Category } ( e : Equivalence C D ) : EssentiallySurjective (e.functor) :=
  λ Y : D.Obj, ⟨ e.inverse.onObjects Y, e.isomorphism_2.components Y ⟩

section FullyFaithfulPreimage

  universes u1 v1 u2 v2
  parameters { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  parameter ( F : Functor C D )
  parameters ( full : Full F ) ( faithful : Faithful F )

  lemma preimage_identity ( X : C.Obj ) : full.preimage (D.identity (F.onObjects X)) = C.identity X :=
    faithful.injectivity (full.preimage (D.identity (F.onObjects X))) (C.identity X) $
      calc
        F.onMorphisms (full.preimage (D.identity (F.onObjects X)))
            = D.identity (F.onObjects X) : full.witness (D.identity (F.onObjects X))
        ... = F.onMorphisms (C.identity X) : ♮

  lemma preimage_functoriality
    { X Y Z : C.Obj }
    ( f : D.Hom (F.onObjects X) (F.onObjects Y) )
    ( g : D.Hom (F.onObjects Y) (F.onObjects Z) ) :
    C.compose (full.preimage f) (full.preimage g) = full.preimage (D.compose f g) :=
    faithful.injectivity (C.compose (full.preimage f) (full.preimage g)) (full.preimage (D.compose f g)) $
      calc
        F.onMorphisms (C.compose (full.preimage f) (full.preimage g))
            = D.compose (F.onMorphisms (full.preimage f)) (F.onMorphisms (full.preimage g)) : ♮
        ... = D.compose f g
            : by rewrite [full.witness f, full.witness g]
        ... = F.onMorphisms (full.preimage (D.compose f g))
            : by rewrite full.witness (D.compose f g)

  lemma preimage_composition_identity
    { X Y : C.Obj }
    ( f : D.Hom (F.onObjects X) (F.onObjects Y) )
    ( g : D.Hom (F.onObjects Y) (F.onObjects X) )
    ( eq : D.compose f g = D.identity (F.onObjects X) ) :
    C.compose (full.preimage f) (full.preimage g) = C.identity X :=
      calc
        C.compose (full.preimage f) (full.preimage g)
            = full.preimage (D.compose f g)              : preimage_functoriality f g
        ... = full.preimage (D.identity (F.onObjects X)) : by rewrite eq
        ... = C.identity X                               : preimage_identity X

  definition preimage_isomorphism { X Y : C.Obj } ( f : Isomorphism D (F.onObjects X) (F.onObjects Y) ) : Isomorphism C X Y := {
    morphism := full.preimage f.morphism,
    inverse := full.preimage f.inverse,
    witness_1 := preimage_composition_identity f.morphism f.inverse f.witness_1,
    witness_2 := preimage_composition_identity f.inverse f.morphism f.witness_2
  }

end FullyFaithfulPreimage

private definition {u1 v1 u2 v2} preimage
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( e : Equivalence C D )
  ( X Y : C.Obj )
  ( h : D.Hom (e.functor.onObjects X) (e.functor.onObjects Y) ) :=
  C.compose (C.compose (e.isomorphism_1.inverse.components X) (e.inverse.onMorphisms h)) (e.isomorphism_1.morphism.components Y)

private lemma {u1 v1 u2 v2} preimage_is_retraction
  { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  ( e : Equivalence C D )
  ( X Y : C.Obj )
  ( f : C.Hom X Y ) :
  preimage e X Y (e.functor.onMorphisms f) = f :=
  e.isomorphism_1.naturality_1 f

private lemma {u v} sections_are_injective
  { A : Type u } { B : Type v }
  ( f : A → B ) ( g : B → A )
  ( f_section_of_g : ∀ (a : A), g (f a) = a )
  ( a b : A )
  ( H : f a = f b ) :
  a = b :=
    calc
      a   = g (f a) : eq.symm (f_section_of_g a)
      ... = g (f b) : congr_arg g H
      ... = b       : f_section_of_g b

lemma {u1 v1 u2 v2} Equivalences_are_Faithful { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( e : Equivalence C D ) : Faithful (e.functor) := {
  injectivity :=
    λ {X Y : C.Obj} (f g : C.Hom X Y),
      sections_are_injective (@Functor.onMorphisms _ _ e.functor X Y) (preimage e X Y) (preimage_is_retraction e X Y) f g
}

@[simp] private lemma {u1 v1 u2 v2} preimage_lemma { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( e : Equivalence C D ) ( X Y : C.Obj ) ( h : D.Hom (e.functor.onObjects X) (e.functor.onObjects Y) ) : (e.inverse).onMorphisms ((e.functor).onMorphisms (preimage e X Y h)) = (e.inverse).onMorphisms h :=
begin
  erewrite ← e.isomorphism_1.naturality_2 (preimage e X Y h),
  repeat_at_least_once { erewrite ← C.associativity },
  -- tidy, -- PROJECT this used to work!
  erewrite e.isomorphism_1.componentwise_witness_1,
  repeat_at_least_once { rewrite C.associativity },
  erewrite e.isomorphism_1.componentwise_witness_1,
  erewrite C.right_identity,
  rewrite C.left_identity
end

lemma {u1 v1 u2 v2} Equivalences_are_Full { C : Category.{u1 v1} } { D : Category.{u2 v2} } ( e : Equivalence C D ) : Full (e.functor) :=
  {
    preimage := preimage e,
    witness := 
        begin 
          intros X Y h,
          apply (Equivalences_are_Faithful e.reverse).injectivity,
          tidy,
        end
  }

section FullyFaithfulEssentiallySurjective_Functors_are_Equivalences

  universes u1 v1 u2 v2
  parameters { C : Category.{u1 v1} } { D : Category.{u2 v2} }
  parameter ( F : Functor C D )
  parameter ( full : Full F )
  parameter ( faithful : Faithful F )
  parameter ( ess_surj : EssentiallySurjective F )

  local infixl `⟩C⟩`:60 := C.compose
  local infixl `⟩D⟩`:60 := D.compose

  def G_onObjects : D.Obj → C.Obj :=
    λ X : D.Obj,
      (ess_surj X).1
  
  @[reducible] def ε_mor (X : D.Obj) : D.Hom (F.onObjects (G_onObjects X)) X :=
    (ess_surj X).2.morphism
  
  @[reducible] def ε_inv (X : D.Obj) : D.Hom X (F.onObjects (G_onObjects X)) :=
    (ess_surj X).2.inverse
  
  def G_onMorphisms : Π {X Y : D.Obj}, D.Hom X Y → C.Hom (G_onObjects X) (G_onObjects Y) :=
    λ {X Y : D.Obj} g : D.Hom X Y,
      let g' := ε_mor X ⟩D⟩ g ⟩D⟩ ε_inv Y
      in full.preimage g'

  definition G : Functor D C := {
    onObjects := G_onObjects,
    onMorphisms := λ {X Y : D.Obj}, G_onMorphisms,
    identities :=
      λ (X : D.Obj),
        let g' := ε_mor X ⟩D⟩ D.identity X ⟩D⟩ ε_inv X in
        calc
          full.preimage g'
              = full.preimage (D.identity (F.onObjects (G_onObjects X))) : ♮
          ... = C.identity (G_onObjects X)
              : preimage_identity F full faithful (G_onObjects X),
    functoriality :=
      λ {X Y Z : D.Obj} (f : D.Hom X Y) (g : D.Hom Y Z),
        faithful.injectivity (G_onMorphisms (f ⟩D⟩ g)) (G_onMorphisms f ⟩C⟩ G_onMorphisms g) $
          let f'  := ε_mor X ⟩D⟩ f ⟩D⟩ ε_inv Y,
              g'  := ε_mor Y ⟩D⟩ g ⟩D⟩ ε_inv Z,
              fg' := ε_mor X ⟩D⟩ (f ⟩D⟩ g) ⟩D⟩ ε_inv Z in
          calc
            F.onMorphisms (full.preimage fg')
                = fg' : full.witness fg'
            ... = (ε_mor X ⟩D⟩ f) ⟩D⟩ D.identity Y ⟩D⟩ (g ⟩D⟩ ε_inv Z) : ♮
            ... = (ε_mor X ⟩D⟩ f) ⟩D⟩ (ε_inv Y ⟩D⟩ ε_mor Y) ⟩D⟩ (g ⟩D⟩ ε_inv Z)
                : by rewrite Isomorphism.witness_2_lemma (ess_surj Y).2
            ... = f' ⟩D⟩ g' : by repeat_at_least_once { rewrite ← D.associativity }
            ... = F.onMorphisms (full.preimage f') ⟩D⟩ F.onMorphisms (full.preimage g')
                : by rewrite [full.witness f', full.witness g']
            ... = F.onMorphisms (full.preimage f' ⟩C⟩ full.preimage g') : ♮
  }

  lemma ε_natural {X Y : D.Obj} (f : D.Hom X Y) : F.onMorphisms (G.onMorphisms f) ⟩D⟩ ε_mor Y = ε_mor X ⟩D⟩ f :=
    let f' := ε_mor X ⟩D⟩ f ⟩D⟩ ε_inv Y in
    calc
      F.onMorphisms (full.preimage f') ⟩D⟩ ε_mor Y
          = f' ⟩D⟩ ε_mor Y
          : by rewrite full.witness f'
      ... = ε_mor X ⟩D⟩ f
          : by rewrite [D.associativity, Isomorphism.witness_2_lemma (ess_surj Y).2, D.right_identity]

  definition ε : NaturalIsomorphism (FunctorComposition G F) (IdentityFunctor D) :=
    NaturalIsomorphism.from_components (λ X, (ess_surj X).2) (λ {X Y : D.Obj}, ε_natural)

  def η_comp (X : C.Obj) : Isomorphism C (G.onObjects (F.onObjects X)) X :=
    preimage_isomorphism F full faithful (NaturalIsomorphism.components ε (F.onObjects X))

  lemma η_natural {X Y : C.Obj} (f : C.Hom X Y) : G.onMorphisms (F.onMorphisms f) ⟩C⟩ (η_comp Y).morphism = (η_comp X).morphism ⟩C⟩ f :=
    faithful.injectivity (G.onMorphisms (F.onMorphisms f) ⟩C⟩ (η_comp Y).morphism) ((η_comp X).morphism ⟩C⟩ f) $
      let H := full.witness (ε_mor (F.onObjects X)) in
      calc
        F.onMorphisms (G.onMorphisms (F.onMorphisms f) ⟩C⟩ (η_comp Y).morphism)
            = F.onMorphisms (G.onMorphisms (F.onMorphisms f)) ⟩D⟩ F.onMorphisms (full.preimage (ε_mor (F.onObjects Y)))
            : F.functoriality _ _
        ... = F.onMorphisms (G.onMorphisms (F.onMorphisms f)) ⟩D⟩ ε_mor (F.onObjects Y)
            : congr_arg (λ k, F.onMorphisms (G.onMorphisms (F.onMorphisms f)) ⟩D⟩ k) (full.witness (ε_mor (F.onObjects Y)))
        ... = ε_mor (F.onObjects X) ⟩D⟩ F.onMorphisms f
            : ε.morphism.naturality (F.onMorphisms f)
        ... = F.onMorphisms (full.preimage (ε_mor (F.onObjects X))) ⟩D⟩ F.onMorphisms f
            : eq.symm $ congr_arg (λ k, k ⟩D⟩ F.onMorphisms f) $ full.witness (ε_mor (F.onObjects X))
        ... = F.onMorphisms ((η_comp X).morphism ⟩C⟩ f)
            : eq.symm (F.functoriality _ _)

  definition η : NaturalIsomorphism (FunctorComposition F G) (IdentityFunctor C) :=
    NaturalIsomorphism.from_components η_comp (λ {X Y : C.Obj}, η_natural)

  definition equivalence : Equivalence C D := {
    functor := F,
    inverse := G,
    isomorphism_1 := η,
    isomorphism_2 := ε
  }

  definition is_equivalence : is_Equivalence F := ⟨equivalence, by reflexivity⟩

end FullyFaithfulEssentiallySurjective_Functors_are_Equivalences

end categories.equivalence