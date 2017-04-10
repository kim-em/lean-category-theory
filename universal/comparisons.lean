-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ..isomorphism
import ..natural_transformation
import ..examples.types.types
import ..equivalence
import .comma_categories
import .universal


open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.equivalence
open tqft.categories.examples.types
open tqft.categories.universal

namespace tqft.categories.universal

-- This works fine; commented out for speed.
-- definition Cones_agree { J C : Category } ( F: Functor J C ) : Isomorphism CategoryOfTypes (comma.Cones F).Obj (Cone F) := {
--   morphism := λ C, {
--     limit         := C.1,
--     maps          := λ j : J.Obj, (C.2.2).components j,
--     commutativity := λ ( j k : J.Obj ) ( f : J.Hom j k ), begin
--                                                             refine ( cast _ (eq.symm ((C.2.2).naturality f)) ),
--                                                             unfold_unfoldable,
--                                                             simp
--                                                           end
--   },
--   inverse := λ C, ⟨ C.limit, ♯, {
--     components := λ j, C.maps j,
--     naturality := λ _ _ f, begin refine ( cast _ (eq.symm (C.commutativity f)) ), unfold_unfoldable, simp end
--   } ⟩,
--   witness_1 := begin
--                  -- PROJECT gross, but looks automatable.
--                 --  unfold_unfoldable,
--                 --  apply funext,
--                 --  intros,
--                 --  simp,
--                 --  fapply dependent_pair_equality,
--                 --  simp,
--                 --  reflexivity,
--                 --  induction x with x_1 x_23,
--                 --  induction x_23 with x_2 x_3,
--                 --  induction x_2,
--                 --  unfold_unfoldable_hypotheses,                 
--                 --  simp,
--                 --  fapply dependent_pair_equality,
--                 --  reflexivity,
--                 --  simp,
--                 --  apply natural_transformation.NaturalTransformations_componentwise_equal,
--                 --  intros,
--                 --  dsimp,
--                 --  reflexivity,
--                end,
--   witness_2 := begin
--                  unfold_unfoldable,
--                  apply funext,
--                  intros,
--                  simp,
                 
--                end
-- }

definition comma_Cone_to_Cone { J C : Category } { F : Functor J C } ( cone : (comma.Cones F).Obj ) : Cone F := 
{
  limit         := cone.1,
  maps          := λ j : J.Obj, (cone.2.2).components j,
  commutativity := λ ( j k : J.Obj ) ( f : J.Hom j k ),
                      begin
                        refine ( cast _ (eq.symm ((cone.2.2).naturality f)) ),
                        unfold_unfoldable,
                        simp
                      end
}


definition comma_ConeMorphism_to_ConeMorphism { J C : Category } { F : Functor J C } { X Y : (comma.Cones F).Obj } ( f : (comma.Cones F).Hom X Y ) : ConeMorphism (comma_Cone_to_Cone X) (comma_Cone_to_Cone Y) := 
{
  morphism      := f.val.1,
  commutativity := λ j : J.Obj, begin
                                  blast, 
                                  induction X with X1 X23,
                                  induction X23 with X2 X3, 
                                  induction X2,
                                  induction Y with Y1 Y23, 
                                  induction Y23 with Y2 Y3, 
                                  induction Y2,
                                  induction f with T p,
                                  induction T with T_1,
                                  dsimp,  
                                  pose q := congr_arg (λ t : NaturalTransformation _ _, t.components j) p,
                                  simp at q,
                                  dsimp at q,
                                  unfold_unfoldable_hypotheses,
                                  rewrite q,
                                  blast
                                end
}

definition Cone_to_comma_Cone { J C : Category } { F : Functor J C } ( cone : Cone F ) : (comma.Cones F).Obj := 
⟨ cone.limit, ♯, {
    components := λ j, cone.maps j,
    naturality := λ _ _ f, begin
                            refine ( cast _ (eq.symm (cone.commutativity f)) ), 
                            unfold_unfoldable, 
                            simp
                          end
  } ⟩

definition ConeMorphism_to_comma_ConeMorphism { J C : Category } { F : Functor J C } { X Y : Cone F } ( f : ConeMorphism X Y ) : (comma.Cones F).Hom (Cone_to_comma_Cone X) (Cone_to_comma_Cone Y) := 
  ⟨ (f.morphism, ♯), ♯ ⟩

definition comma_Cones_to_Cones { J C : Category } ( F : Functor J C ) : Functor (comma.Cones F) (Cones F) := {
    onObjects     := comma_Cone_to_Cone,
    onMorphisms   := λ _ _ f, comma_ConeMorphism_to_ConeMorphism f,
    identities    := ♯,
    functoriality := ♯
  }

definition Cones_to_comma_Cones { J C : Category } ( F : Functor J C ) : Functor (Cones F) (comma.Cones F) := {
    onObjects     := Cone_to_comma_Cone,
    onMorphisms   := λ _ _ f, ConeMorphism_to_comma_ConeMorphism f,
    identities    := ♯,
    functoriality := ♯
  }

lemma Equalizers_agree { C : Category } { α β : C.Obj } ( f g : C.Hom α β )
 : @Isomorphism CategoryOfTypes (comma.Equalizer f g) (Equalizer f g) :=
 {
  morphism := sorry,  
  inverse  := sorry,
  witness_1 := sorry,
  witness_2 := sorry
}

-- lemma Equalizers_are_unique
--   { C : Category }  
--   { X Y : C.Obj } 
--   ( f g : C.Hom X Y )
--    : unique_up_to_isomorphism (Equalizer f g) Equalizer.equalizer
--    := λ (E1 E2 : Equalizer f g), 
--        comma.InitialObjects_are_unique (Isomorphism.inverse (Equalizers_agree f g) E1) ((Equalizers_agree f g).inverse E2)

end tqft.categories.universal