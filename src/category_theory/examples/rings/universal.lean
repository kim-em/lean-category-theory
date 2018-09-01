import ring_theory.ideals
import linear_algebra.quotient_module
import category_theory.examples.rings
import category_theory.universal.limits.limits
import category_theory.universal.limits
import category_theory.universal.colimits
import category_theory.filtered

universes v

namespace category_theory.examples

open category_theory
open category_theory.universal

variables {α : Type v}

instance : has_products.{v+1 v} Ring := sorry

def coequalizer_ideal {R S : Ring} (f g : ring_hom R S) : set S.1 :=
span (set.range (λ x : R.1, f.map x - g.map x))

instance {R S : Ring} (f g : ring_hom R S) : is_ideal (coequalizer_ideal f g) := sorry

local attribute [instance] classical.prop_decidable

instance : has_coequalizers.{v+1 v} Ring :=
{ coequalizer := λ R S f g, 
    { X := ⟨ quotient_ring.quotient (coequalizer_ideal f g), by apply_instance ⟩,
      π := ⟨ quotient_ring.mk, by apply_instance ⟩,
      w := sorry /- almost there: -/
        /- begin 
             ext, dsimp, apply quotient.sound, fsplit, 
             exact finsupp.single 1 (f.map x - g.map x), obviously, 
             sorry, sorry 
           end -/ },
  is_coequalizer := λ R S f g, 
    { desc := λ s,
      { map := sorry, 
        is_ring_hom := sorry, }, 
      fac := sorry, 
      uniq := sorry }
}

instance : has_colimits.{v+1 v} Ring := sorry

section
variables {J : Type v} [𝒥 : small_category J] [filtered.{v v} J]
include 𝒥

def matching (F : J ↝ Ring) (a b : Σ j : J, (F j).1) : Prop :=
let s := filtered.obj_bound.{v v} a.1 b.1 in
(F.map(s.ι₁)).map a.2 = (F.map(s.ι₂)).map b.2

def filtered_colimit (F : J ↝ Ring) :=
quotient (eqv_gen.setoid (matching F))

def filtered_colimit_is_comm_ring (F : J ↝ Ring) : comm_ring (filtered_colimit F) := 
sorry

end

instance : has_filtered_colimits.{v+1 v} Ring :=
{ colimit := λ J 𝒥 f F,
  begin
    resetI, exact 
    { X := ⟨ filtered_colimit F, filtered_colimit_is_comm_ring F ⟩,
      ι := λ j, { map := λ x, begin sorry end, 
                  is_ring_hom := sorry },
      w := sorry, }
  end,
  is_colimit := sorry }

end category_theory.examples