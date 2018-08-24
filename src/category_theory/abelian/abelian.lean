-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.abelian.monic
import category_theory.universal.monic
import category_theory.universal.kernels

open category_theory
open category_theory.universal
open category_theory.universal.monic

namespace category_theory.abelian

-- This is the def of abelian from Etingof's "Tensor categories"

universes u v

-- structure KernelImageCokernelDecomposition 
--   {C : Type u} [category.{u v} C] [has_zero_object.{u v} C] [has_kernels.{u v} C] [has_cokernels.{u v} C]
--   {X Y : C} (f : X ⟶ Y) :=
--   (image_well_defined      : cokernel (kernel.map f) ≅ kernel (cokernel.map f))
--   (composition_is_morphism : (cokernel (kernel.map f)).map ≫ image_well_defined.hom ≫ (kernel (cokernel.map f)).map = f)

-- class Abelian {C : Type u} [category.{u v} C] [has_zero_object.{u v} C] [has_kernels.{u v} C] [has_cokernels.{u v} C] := 
--   (decomposition : ∀ {X Y : C} (f : X ⟶ Y), KernelImageCokernelDecomposition f)

-- This is the usual definition

class Abelian' {C : Type u} [category.{u v} C] [has_zero_object.{u v} C] :=
  (monics_are_regular : ∀ {X Y : C} {f : X ⟶ Y} (m : mono f), regular_mono f)
  (epics_are_regular  : ∀ {X Y : C} {f : X ⟶ Y} (m : epi f ), regular_epi  f)
  
-- PROJECT show these definitions are equivalent

-- PROJECT define short and long exact sequences, cohomology?

end category_theory.abelian