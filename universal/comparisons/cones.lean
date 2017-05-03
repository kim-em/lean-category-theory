-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...isomorphism
import ...natural_transformation
import ...examples.types.types
import ...equivalence
import ..comma_categories
import ..universal

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.equivalence
open tqft.categories.examples.types
open tqft.categories.universal

namespace tqft.categories.universal

definition comma_Cone_to_Cone { J C : Category } { F : Functor J C } ( cone : (comma.Cones F).Obj ) : Cone F := 
{
  limit         := cone.1,
  maps          := λ j : J.Obj, (cone.2.2).components j,
  commutativity := λ ( j k : J.Obj ) ( f : J.Hom j k ),
                      begin
                          -- PROJECT write an `its` tactic
                        refine ( cast _ (eq.symm ((cone.2.2).naturality f)) ),
                        tidy
                      end
}

definition comma_ConeMorphism_to_ConeMorphism { J C : Category } { F : Functor J C } { X Y : (comma.Cones F).Obj } ( f : (comma.Cones F).Hom X Y ) : ConeMorphism (comma_Cone_to_Cone X) (comma_Cone_to_Cone Y) := 
{
  morphism      := f.val.1,
  commutativity := λ j : J.Obj, begin
   -- PROJECT improve automation further?
                                  tidy,
                                  -- induction f with T p,
                                  pose q := congr_arg (λ t : NaturalTransformation _ _, t.components j) f_2,
                                  blast
                                end
}

definition Cone_to_comma_Cone { J C : Category } { F : Functor J C } ( cone : Cone F ) : (comma.Cones F).Obj := 
⟨ cone.limit, ♯, {
    components := λ j, cone.maps j,
    naturality := λ _ _ f, begin
    -- PROJECT write an `its` tactic
                            refine ( cast _ (eq.symm (cone.commutativity f)) ), 
                            tidy
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

definition Cones_agree { J C : Category } ( F : Functor J C ) : Equivalence (comma.Cones F) (Cones F) := {
  functor := comma_Cones_to_Cones F,
  inverse := Cones_to_comma_Cones F,
  isomorphism_1 := ♯,
  isomorphism_2 := ♯
}

-- lemma Equalizers_agree { C : Category } { α β : C.Obj } ( f g : C.Hom α β )
--  : @Isomorphism CategoryOfTypes (comma.Equalizer f g) (Equalizer f g) :=
--  {
--   morphism := sorry,  
--   inverse  := sorry,
--   witness_1 := sorry,
--   witness_2 := sorry
-- }

-- lemma Equalizers_are_unique
--   { C : Category }  
--   { X Y : C.Obj } 
--   ( f g : C.Hom X Y )
--    : unique_up_to_isomorphism (Equalizer f g) Equalizer.equalizer
--    := λ (E1 E2 : Equalizer f g), 
--        comma.InitialObjects_are_unique (Isomorphism.inverse (Equalizers_agree f g) E1) ((Equalizers_agree f g).inverse E2)

end tqft.categories.universal