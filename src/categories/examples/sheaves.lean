import ..functor
import ..opposites
import .topological_spaces
import ..types
import data.set.basic

open categories
open categories.functor
open categories.types
open categories.opposites
open categories.examples.topological_spaces

namespace categories.examples.sheaves

def Presheaf { α } ( X : topological_space α ) := Functor (Opposite (topological_space.to_category X)) CategoryOfTypes

structure OpenCovering { α } ( X : topological_space α ) :=
  ( I   : Type )
  ( U : I → OpenSets X )

-- FIXME these lemmas are already marked as simp. Why aren't they successfully used by tidy?
local attribute [applicable] set.inter_subset_left set.inter_subset_right

private definition intersection_inclusion_1 { α } { X : topological_space α } { C : OpenCovering X } ( i j : C.I ) : (C.U i ∩ C.U j) ⊆ (C.U i) := ♯ 
private definition intersection_inclusion_2 { α } { X : topological_space α } { C : OpenCovering X } ( i j : C.I ) : (C.U i ∩ C.U j) ⊆ (C.U j) := ♯

-- we need to give instance resolution a little help, realising that the opposite category has the same objects.
private definition opposite_has_inter { C : Category } [ w : has_inter C.Obj ] : has_inter ((Opposite C).Obj) := w
local attribute [instance] opposite_has_inter

private definition restriction_to_intersection_1
  { α } { X : topological_space α } 
  { C : OpenCovering X } 
  ( i j : C.I ) 
  ( F : Presheaf X ) : (F.onObjects (C.U i)) → (F.onObjects ((C.U i) ∩ (C.U j))) := 
F.onMorphisms (plift.up (intersection_inclusion_1 i j))

private definition restriction_to_intersection_2
  { α } { X : topological_space α } 
  { C : OpenCovering X } 
  ( i j : C.I ) 
  ( F : Presheaf X ) : (F.onObjects (C.U j)) → (F.onObjects ((C.U i) ∩ (C.U j))) := 
F.onMorphisms (plift.up (intersection_inclusion_2 i j))

structure CompatibleSections { α } { X : topological_space α } ( covering : OpenCovering X ) ( F : Presheaf X ) := 
  ( sections      : Π i : covering.I, F.onObjects (covering.U i) )
  ( compatibility : Π i j : covering.I, restriction_to_intersection_1 i j F (sections i) = restriction_to_intersection_2 i j F (sections j) )

-- definition OpenCovering.union { α } { X : topological_space α } ( covering : OpenCovering X ) : OpenSets X := sorry
-- definition OpenCovering.union_inclusion { α } { X : topological_space α } ( covering : OpenCovering X ) ( i : covering.I ) : covering.U i ⊆ covering.union := sorry

-- structure Gluing { α } { X : topological_space α } { U : OpenCovering X } { F : Presheaf X } ( s : CompatibleSections U F ) :=
--   ( section_     : F.onObjects U.union )
--   ( restrictions : ∀ i : U.I, F.onMorphisms (plift.up (U.union_inclusion i)) section_ = s.sections i)

-- structure Sheaf { α } ( X : topological_space α ) :=
--   ( presheaf        : Presheaf X )
--   ( sheaf_condition : Π (U : OpenCovering X) ( s : CompatibleSections U presheaf ), Gluing s )

end categories.examples.sheaves