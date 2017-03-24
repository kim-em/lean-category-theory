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

@[pointwise] lemma ModuleMorphism_pointwisewise_equal
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

local attribute [reducible] lift_t coe_t coe_b

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

structure MonoidObject ( C : MonoidalCategory ) extends SemigroupObject C := 
  ( unit : C^.Hom C^.tensor_unit object )
  ( left_identity  : C^.compose (C^.left_unitor_is_isomorphism^.inverse object)  (C^.compose (C^.tensorMorphisms unit (C^.identity object)) multiplication) = C^.identity object )
  ( right_identity : C^.compose (C^.right_unitor_is_isomorphism^.inverse object) (C^.compose (C^.tensorMorphisms (C^.identity object) unit) multiplication) = C^.identity object )

attribute [simp,ematch] MonoidObject.left_identity
attribute [simp,ematch] MonoidObject.right_identity

-- instance MonoidObject_coercion_to_SemigroupObject { C : MonoidalCategory } : has_coe (MonoidObject C) (SemigroupObject C) :=
--   { coe := MonoidObject.to_SemigroupObject }

set_option pp.universes true

structure ModuleObject { C : MonoidalCategory } ( A : MonoidObject C ) extends SemigroupModuleObject A^.to_SemigroupObject :=
  ( identity  : C^.compose (C^.left_unitor_is_isomorphism^.inverse module)  (C^.compose (C^.tensorMorphisms A^.unit (C^.identity module)) action) = C^.identity module )

attribute [simp,ematch] ModuleObject.identity
attribute [ematch] ModuleObject.associativity

structure ModuleMorphism { C : MonoidalCategory } { A : MonoidObject C } ( X Y : ModuleObject A ) extends SemigroupModuleMorphism X^.to_SemigroupModuleObject Y^.to_SemigroupModuleObject

attribute [ematch,simp] SemigroupModuleMorphism.compatibility

definition CategoryOfModules { C: MonoidalCategory } ( A : MonoidObject C ) : Category :=
{
  Obj := ModuleObject A,
  Hom := λ X Y, ModuleMorphism X Y,
  identity := λ X, ⟨ C^.identity X^.module, ♮ ⟩,
  compose  := λ _ _ _ f g, ⟨ C^.compose f^.map g^.map, begin blast, end ⟩,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

-- definition CategoryOfFreeModules { C : MonoidalCategory } ( A : MonoidObject C ) : Category :=
-- {
--   Obj := C^.Obj,
--   Hom := λ X Y, C^.Hom X (C^.tensorObjects A^.object Y),
--   identity := λ X, C^.compose (C^.left_unitor_is_isomorphism^.inverse X) (C^.tensorMorphisms A^.unit (C^.identity X)),
--   compose := λ _ _ Z f g, C^.compose (C^.compose (C^.compose f (C^.tensorMorphisms (C^.identity A^.object) g)) (C^.inverse_associator A^.object A^.object Z)) (C^.tensorMorphisms A^.multiplication (C^.identity Z)),
--   left_identity := begin
--                     -- blast, -- TODO this seems to run forever
--                     exact sorry
--                    end,
--   right_identity := sorry,
--   associativity := sorry
-- }


-- PROJECT show that after idempotent completing the category of free modules we get the category of modules??
-- PROJECT bimodules
-- PROJECT commutative algebras; modules give bimodules

end tqft.categories.internal_objects