-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..universal.universal

open tqft.categories
open tqft.categories.initial
open tqft.categories.universal
open tqft.categories.isomorphism

namespace tqft.categories.abelian

-- This is the definition of abelian from Etingof's "Tensor categories"

structure KernelImageCokernelSequence { C : Category } [ ZeroObject C ] { X Y : C.Obj } ( f : C.Hom X Y ) :=
  ( kernel                  : Kernel f   )
  ( cokernel                : Cokernel f )
  ( cokernel_of_kernel      : Cokernel (kernel.inclusion)  )
  ( kernel_of_cokernel      : Kernel (cokernel.projection) )
  ( image_well_defined      : Isomorphism C cokernel_of_kernel.coequalizer kernel_of_cokernel.equalizer )
  ( composition_is_morphism : C.compose (C.compose cokernel_of_kernel.projection image_well_defined.morphism) kernel_of_cokernel.inclusion = f )

structure Abelian ( C : Category ) [ ZeroObject C ] := 
  ( decomposition : ∀ { X Y : C.Obj } ( f : C.Hom X Y ), KernelImageCokernelSequence f )

end tqft.categories.abelian