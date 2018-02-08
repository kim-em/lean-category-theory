-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..functor
import ..opposites
import .topological_spaces
import ..universal.strongly_concrete
import ..examples.rings

open categories
open categories.functor
open categories.types
open categories.opposites
open categories.examples.topological_spaces

namespace categories.examples.sheaves

def {u v w} PresheafOf ( C : Category.{u v} ) { α : Type w } ( X : topological_space α ) := Functor (Opposite (X.OpenSets)) C
def {w} Presheaf { α : Type w } ( X : topological_space α ) := PresheafOf CategoryOfTypes X

structure OpenCovering { α } ( X : topological_space α ) :=
  ( I   : Type )
  ( U : I → OpenSet X )

definition OpenCovering.union { α } { X : topological_space α } ( covering : OpenCovering X ) : OpenSet X := let U := (set.range (λ i, (covering.U i).underlying_set)) in {
  underlying_set := ⋃₀ U,
  is_open := X.is_open_sUnion
               U
               (begin intros, dsimp [U] at H, unfold set.range at H, simp at H, induction H with i r, rw ← r, exact (covering.U i).is_open end)            
}
definition OpenCovering.union_inclusion { α } { X : topological_space α } ( covering : OpenCovering X ) ( i : covering.I ) : covering.U i ⊆ covering.union := 
begin
  apply set.subset_sUnion_of_mem,
  apply set.mem_range_self,
end

-- PROJECT these lemmas are already marked as simp. Why aren't they successfully used by tidy?
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
  { D : Category }
  ( F : PresheafOf D X ) : D.Hom (F.onObjects (C.U i)) (F.onObjects ((C.U i) ∩ (C.U j))) := 
F.onMorphisms (ulift.up (plift.up (intersection_inclusion_1 i j)))

private definition restriction_to_intersection_2
  { α } { X : topological_space α } 
  { C : OpenCovering X } 
  ( i j : C.I ) 
  { D : Category }
  ( F : PresheafOf D X ) : D.Hom (F.onObjects (C.U j)) (F.onObjects ((C.U i) ∩ (C.U j))) := 
F.onMorphisms (ulift.up (plift.up (intersection_inclusion_2 i j)))

structure CompatibleSections { α } { X : topological_space α } ( covering : OpenCovering X ) ( F : Presheaf X ) := 
  ( sections      : Π i : covering.I, F.onObjects (covering.U i) )
  ( compatibility : Π i j : covering.I, restriction_to_intersection_1 i j F (sections i) = restriction_to_intersection_2 i j F (sections j) )

structure Gluing { α } { X : topological_space α } { U : OpenCovering X } { F : Presheaf X } ( s : CompatibleSections U F ) :=
  ( section_     : F.onObjects U.union )
  ( restrictions : ∀ i : U.I, F.onMorphisms (ulift.up (plift.up (U.union_inclusion i))) section_ = s.sections i)

structure Sheaf { α } ( X : topological_space α ) :=
  ( presheaf        : Presheaf X )
  ( sheaf_condition : Π ( U : OpenCovering X ) ( s : CompatibleSections U presheaf ), Gluing s )

open categories.universal

structure {u₁ u₂ u₃ u₄} NaiveSheafOf ( C : Category.{u₁ u₂} ) { α : Type u₃ } ( X : topological_space α ) [ sc : StronglyConcrete.{u₁ u₂ u₄ u₃ u₃} C ] :=
  ( presheaf        : PresheafOf C X )
  ( sheaf_condition : Π ( U : OpenCovering X ) ( s : CompatibleSections U (FunctorComposition presheaf sc.F) ), Gluing s )

open categories.examples.rings

-- PROJECT work out why typeclass inference is failing here: we shouldn't have to use @ below, or specify CommutativeRings_StronglyConcrete

structure {u v} RingedSpace (α : Type u) :=
  ( space : topological_space α )
  ( structure_sheaf : @NaiveSheafOf CategoryOfCommutativeRings.{v} α space CommutativeRings_StronglyConcrete ) 

-- TODO define stalks first (for which Rings needs colimits)
-- structure LocallyRingedSpace (α : Type) extends RingedSpace α :=
--   ( local_rings : ∀ a : α, is_local (stalk_at a structure_sheaf) )

end categories.examples.sheaves