-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor
import category_theory.tactics.obviously

open category_theory

namespace category_theory.examples

universe u₁

def Ring : Type (u₁+1) := Σ α : Type u₁, comm_ring α

instance ring_from_Ring (R : Ring) : comm_ring R.1 := R.2

structure ring_hom (R S : Ring.{u₁}) : Type u₁ :=
(map: R.1 → S.1)
(is_ring_hom : is_ring_hom map . obviously)

instance (R S : Ring.{u₁}) (f : ring_hom R S) : is_ring_hom f.map := f.is_ring_hom

@[simp,search] lemma ring_hom.map_mul (R S : Ring.{u₁}) (f : ring_hom R S) (x y : R.1) : f.map(x * y) = (f.map x) * (f.map y) := by sorry
@[simp,search] lemma ring_hom.map_add (R S : Ring.{u₁}) (f : ring_hom R S) (x y : R.1) : f.map(x + y) = (f.map x) + (f.map y) := by sorry
@[simp,search] lemma ring_hom.map_one (R S : Ring.{u₁}) (f : ring_hom R S) : f.map 1 = 1 := by sorry

def ring_hom.id (R : Ring) : ring_hom R R :=
{ map := id }

@[simp] lemma ring_hom.id_map (R : Ring) (r : R.1) : (ring_hom.id R).map r = r := rfl

def ring_hom.comp {R S T : Ring} (f: ring_hom R S) (g : ring_hom S T) : ring_hom R T :=
{ map := λ x, g.map (f.map x) }

@[simp] lemma ring_hom.comp_map {R S T: Ring} (f : ring_hom R S) (g : ring_hom S T) (r : R.1) : 
  (ring_hom.comp f g).map r = g.map (f.map r) := rfl

@[extensionality] lemma ring_hom.ext {R S : Ring} (f g : ring_hom R S) (w : ∀ x : R.1, f.map x = g.map x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    tidy,
end

instance RING : large_category Ring := 
{ hom  := ring_hom,
  id   := ring_hom.id,
  comp := @ring_hom.comp }

end category_theory.examples
