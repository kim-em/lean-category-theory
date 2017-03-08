-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .monoidal_category

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

structure SemigroupObject ( C : MonoidalCategory ) :=
  ( object         : C^.Obj )
  ( multiplication : C^.Hom (C^.tensor (object, object)) object)
  ( associativity  : C^.compose (C^.tensorMorphisms multiplication (C^.identity object)) multiplication = C^.compose (C^.associator object object object) (C^.compose (C^.tensorMorphisms (C^.identity object) multiplication) multiplication) )

attribute [ematch] SemigroupObject.associativity

instance SemigroupObject_coercion_to_object { C : MonoidalCategory } : has_coe (SemigroupObject C) (C^.Obj) :=
  { coe := SemigroupObject.object }

structure ModuleObject { C : MonoidalCategory } ( A : SemigroupObject C ) :=
  ( module : C^.Obj )
  ( action : C^.Hom (C^.tensorObjects A module) module )
  ( associativity : C^.compose (C^.tensorMorphisms A^.multiplication (C^.identity module)) action = C^.compose (C^.associator A A module) (C^.compose (C^.tensorMorphisms (C^.identity A) action) action) )

attribute [ematch] ModuleObject.associativity

instance ModuleObject_coercion_to_module { C : MonoidalCategory } ( A : SemigroupObject C ) : has_coe (ModuleObject A) (C^.Obj) :=
  { coe := ModuleObject.module }

structure ModuleMorphism { C : MonoidalCategory } { A : SemigroupObject C } ( X Y : ModuleObject A ) :=
  ( map : C^.Hom X Y )
  ( compatibility : C^.compose (C^.tensorMorphisms (C^.identity A) map) Y^.action = C^.compose X^.action map )

attribute [simp] ModuleMorphism.compatibility

instance ModuleMorphism_coercion_to_map { C : MonoidalCategory } { A : SemigroupObject C } ( X Y : ModuleObject A ) : has_coe (ModuleMorphism X Y) (C^.Hom X Y) :=
  { coe := ModuleMorphism.map }

-- local attribute [reducible] lift_t coe_t coe_b

-- TODO wait for better tactics
definition CategoryOfModules { C: MonoidalCategory } ( A : SemigroupObject C ) : Category :=
{
  Obj := ModuleObject A,
  Hom := λ X Y, ModuleMorphism X Y,
  identity := λ X, ⟨ C^.identity X, ♮ ⟩,
  compose  := λ _ _ _ f g, ⟨ C^.compose f^.map g^.map, ♮ ⟩,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

end tqft.categories.internal_objects