import ..functor
import .topological_spaces
import ..types

open categories
open categories.functor
open categories.types
open categories.examples.topological_spaces

namespace categories.examples.sheaves

def Presheaf { α } ( X : topological_space α ) := Functor (topological_space.to_category X) CategoryOfTypes

structure OpenCovering { α } ( X : topological_space α ) :=
  ( I   : Type )
  ( U_i : I → { W : set α // X.is_open W } )

-- definition OpenCovering.U { α } { X : topological_space α } ( covering : OpenCovering X ) : set α := sorry

-- structure CompatibleSections { α } { X : topological_space α } ( covering : OpenCovering X ) ( F : Presheaf X ) := 
--   ( sections      : Π i : covering.I, F.onObjects (covering.U_i i) )
--   ( compatibility : Π i j : covering.I, sorry )

-- structure Sheaf { α } ( X : topological_space α ) :=
--   ( presheaf        : Presheaf X )
--   ( sheaf_condition : Π (U : OpenCovering X) ( s : CompatibleSections U presheaf ), sorry )

end categories.examples.sheaves