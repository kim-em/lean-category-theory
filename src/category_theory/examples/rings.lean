-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.functor
import category_theory.tactics.obviously

open category_theory

namespace category_theory.examples

universe u₁

def CommRing : Type (u₁+1) := Σ α : Type u₁, comm_ring α

instance ring_from_Ring (R : CommRing) : comm_ring R.1 := R.2

structure ring_hom (R S : CommRing.{u₁}) : Type u₁ :=
(map: R.1 → S.1)
(is_ring_hom : is_ring_hom map . obviously)

instance (R S : CommRing.{u₁}) (f : ring_hom R S) : is_ring_hom f.map := f.is_ring_hom

@[simp] lemma ring_hom.map_mul (R S : CommRing.{u₁}) (f : ring_hom R S) (x y : R.1) : f.map(x * y) = (f.map x) * (f.map y) := by rw f.is_ring_hom.map_mul
@[simp] lemma ring_hom.map_add (R S : CommRing.{u₁}) (f : ring_hom R S) (x y : R.1) : f.map(x + y) = (f.map x) + (f.map y) := by rw f.is_ring_hom.map_add
@[simp] lemma ring_hom.map_one (R S : CommRing.{u₁}) (f : ring_hom R S) : f.map 1 = 1 := by rw f.is_ring_hom.map_one

def ring_hom.id (R : CommRing) : ring_hom R R :=
{ map := id }

@[simp] lemma ring_hom.id_map (R : CommRing) (r : R.1) : (ring_hom.id R).map r = r := rfl

def ring_hom.comp {R S T : CommRing} (f: ring_hom R S) (g : ring_hom S T) : ring_hom R T :=
{ map := λ x, g.map (f.map x) }

@[simp] lemma ring_hom.comp_map {R S T: CommRing} (f : ring_hom R S) (g : ring_hom S T) (r : R.1) : 
  (ring_hom.comp f g).map r = g.map (f.map r) := rfl

@[extensionality] lemma ring_hom.ext {R S : CommRing} (f g : ring_hom R S) (w : ∀ x : R.1, f.map x = g.map x) : f = g :=
begin
    induction f with fc,
    induction g with gc,
    tidy,
end

instance : large_category CommRing := 
{ hom  := ring_hom,
  id   := ring_hom.id,
  comp := @ring_hom.comp }

end category_theory.examples
