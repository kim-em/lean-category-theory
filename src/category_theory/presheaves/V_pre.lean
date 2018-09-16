import ring_theory.ideals
import category_theory.presheaves.stalk
import category_theory.presheaves.map
import category_theory.examples.TopRing
import category_theory.sigma_category

open category_theory
open category_theory.limits
open category_theory.examples

universes u v

namespace category_theory.presheaves

-- TODO we should use filtered/directed colimits here, anyway
instance : has_colimits.{u+1 u} CommRing := sorry

def stalks_local (F : Presheaf.{u+1 u} TopRing) : Type u :=
Π x : F, local_ring (((TopRing.forget_to_CommRing).map_presheaf F).stalk_at x)

def V_pre_pre := Σ (F : Presheaf.{u+1 u} TopRing), stalks_local F

example : category.{u+1 u} V_pre_pre := by unfold V_pre_pre; apply_instance
-- category_theory.sigma_category.{u+1 u} stalks_local.{u}

end category_theory.presheaves