-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .semigroups

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

structure SemigroupModuleObject { C : Category } { m : MonoidalStructure C } ( A : SemigroupObject m ) :=
  ( module : C^.Obj )
  ( action : C^.Hom (m^.tensorObjects A module) module )
  ( associativity : C^.compose (m^.tensorMorphisms A^.multiplication (C^.identity module)) action = C^.compose (m^.associator A A module) (C^.compose (m^.tensorMorphisms (C^.identity A) action) action) )

attribute [ematch] SemigroupModuleObject.associativity

instance SemigroupModuleObject_coercion_to_module { C : Category } { m : MonoidalStructure C } ( A : SemigroupObject m ) : has_coe (SemigroupModuleObject A) (C^.Obj) :=
  { coe := SemigroupModuleObject.module }

structure SemigroupModuleMorphism { C : Category } { m : MonoidalStructure C } { A : SemigroupObject m } ( X Y : SemigroupModuleObject A ) :=
  ( map : C^.Hom X Y )
  ( compatibility : C^.compose (m^.tensorMorphisms (C^.identity A) map) Y^.action = C^.compose X^.action map )

attribute [ematch,simp] SemigroupModuleMorphism.compatibility

@[pointwise] lemma SemigroupModuleMorphism_pointwisewise_equal
  { C : Category } 
  { m : MonoidalStructure C } 
  { A : SemigroupObject m }
  { X Y : SemigroupModuleObject A }
  ( f g : SemigroupModuleMorphism X Y )
  ( w : f^.map = g^.map ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

instance SemigroupModuleMorphism_coercion_to_map { C : Category } { m : MonoidalStructure C }  { A : SemigroupObject m } ( X Y : SemigroupModuleObject A ) : has_coe (SemigroupModuleMorphism X Y) (C^.Hom X Y) :=
  { coe := SemigroupModuleMorphism.map }

-- set_option pp.implicit true

definition CategoryOfSemigroupModules { C : Category } { m : MonoidalStructure C } ( A : SemigroupObject m ) : Category :=
{
  Obj := SemigroupModuleObject A,
  Hom := λ X Y, SemigroupModuleMorphism X Y,
  identity := λ X, ⟨ C^.identity X, ♮ ⟩,
  compose  := λ X Y Z f g, ⟨ C^.compose f^.map g^.map, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♮
}

end tqft.categories.internal_objects