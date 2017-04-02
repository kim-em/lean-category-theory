-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .semigroup_modules
import .monoids

open tqft.categories
open tqft.categories.monoidal_category

namespace tqft.categories.internal_objects

structure ModuleObject { C : Category } { m : MonoidalStructure C } ( A : MonoidObject m ) extends SemigroupModuleObject A.to_SemigroupObject :=
-- TODO components
  ( identity  : C.compose (m.left_unitor.inverse.components module)  (C.compose (m.tensorMorphisms A.unit (C.identity module)) action) = C.identity module )

attribute [simp,ematch] ModuleObject.identity
attribute [ematch] ModuleObject.associativity

structure ModuleMorphism { C : Category } { m : MonoidalStructure C } { A : MonoidObject m } ( X Y : ModuleObject A ) extends SemigroupModuleMorphism X.to_SemigroupModuleObject Y.to_SemigroupModuleObject

attribute [ematch,simp] ModuleMorphism.compatibility

@[pointwise] lemma ModuleMorphism_pointwisewise_equal
  { C : Category }
  { m : MonoidalStructure C }
  { A : MonoidObject m }
  { X Y : ModuleObject A }
  ( f g : ModuleMorphism X Y )
  ( w : f.map = g.map ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

definition CategoryOfModules { C : Category } { m : MonoidalStructure C } ( A : MonoidObject m ) : Category :=
{
  Obj := ModuleObject A,
  Hom := λ X Y, ModuleMorphism X Y,
  identity := λ X, ⟨ C.identity X.module, ♮ ⟩,
  compose  := λ _ _ _ f g, ⟨ C.compose f.map g.map, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♮
}

end tqft.categories.internal_objects