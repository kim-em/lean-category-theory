-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.abelian.monic
import categories.universal.monic
import categories.universal.kernels

open category_theory
open category_theory.initial
open category_theory.universal
open category_theory.universal.monic

namespace category_theory.abelian

-- This is the definition of abelian from Etingof's "Tensor categories"

universe u

structure KernelImageCokernelDecomposition {C : Type (u+1)} [large_category C] [has_ZeroObject.{u+1 u} C] {X Y : C} (f : X ⟶ Y) :=
  (kernel                  : Kernel f  )
  (cokernel                : Cokernel f)
  (cokernel_of_kernel      : Cokernel (kernel.inclusion) )
  (kernel_of_cokernel      : Kernel (cokernel.projection))
  (image_well_defined      : cokernel_of_kernel.cokernel ≅ kernel_of_cokernel.kernel)
  (composition_is_morphism : cokernel_of_kernel.projection ≫ image_well_defined.hom ≫ kernel_of_cokernel.inclusion = f)

class Abelian (C : Type (u+1)) [large_category C] [has_ZeroObject.{u+1 u} C] := 
  (decomposition : ∀ {X Y : C} (f : X ⟶ Y), KernelImageCokernelDecomposition f)

-- This is the usual definition

class Abelian' (C : Type (u+1)) [large_category C] [has_ZeroObject.{u+1 u} C] :=
  (kernel   : ∀ {X Y : C} (f : X ⟶ Y), Kernel f  )
  (cokernel : ∀ {X Y : C} (f : X ⟶ Y), Cokernel f)
  (monics_are_regular : ∀ {X Y : C} {f : X ⟶ Y} (m : Monic f), RegularMonic f)
  (epics_are_regular  : ∀ {X Y : C} {f : X ⟶ Y} (m : Epic f ), RegularEpic f )
  
-- PROJECT show these definitions are equivalent

-- PROJECT define short and long exact sequences, cohomology?

end category_theory.abelian