-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .semigroups

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

structure SemigroupModuleObject { C : MonoidalCategory } ( A : SemigroupObject C ) :=
  ( module : C^.Obj )
  ( action : C^.Hom (C^.tensorObjects A module) module )
  ( associativity : C^.compose (C^.tensorMorphisms A^.multiplication (C^.identity module)) action = C^.compose (C^.associator A A module) (C^.compose (C^.tensorMorphisms (C^.identity A) action) action) )

attribute [ematch] SemigroupModuleObject.associativity

instance SemigroupModuleObject_coercion_to_module { C : MonoidalCategory } ( A : SemigroupObject C ) : has_coe (SemigroupModuleObject A) (C^.Obj) :=
  { coe := SemigroupModuleObject.module }

structure SemigroupModuleMorphism { C : MonoidalCategory } { A : SemigroupObject C } ( X Y : SemigroupModuleObject A ) :=
  ( map : C^.Hom X Y )
  ( compatibility : C^.compose (C^.tensorMorphisms (C^.identity A) map) Y^.action = C^.compose X^.action map )

attribute [ematch,simp] SemigroupModuleMorphism.compatibility

@[pointwise] lemma SemigroupModuleMorphism_pointwisewise_equal
  { C : MonoidalCategory }
  { A : SemigroupObject C }
  { X Y : SemigroupModuleObject A }
  ( f g : SemigroupModuleMorphism X Y )
  ( w : f^.map = g^.map ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

instance SemigroupModuleMorphism_coercion_to_map { C : MonoidalCategory } { A : SemigroupObject C } ( X Y : SemigroupModuleObject A ) : has_coe (SemigroupModuleMorphism X Y) (C^.Hom X Y) :=
  { coe := SemigroupModuleMorphism.map }

definition CategoryOfSemigroupModules { C: MonoidalCategory } ( A : SemigroupObject C ) : Category :=
{
  Obj := SemigroupModuleObject A,
  Hom := λ X Y, SemigroupModuleMorphism X Y,
  identity := λ X, ⟨ C^.identity X, ♮ ⟩,
  compose  := λ _ _ _ f g, ⟨ C^.compose f^.map g^.map, ♮ ⟩,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

end tqft.categories.internal_objects