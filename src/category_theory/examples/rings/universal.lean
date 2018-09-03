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

instance : has_products.{v+1 v} CommRing := sorry

def coequalizer_ideal {R S : CommRing} (f g : ring_hom R S) : set S.1 :=
span (set.range (λ x : R.1, f.map x - g.map x))

instance {R S : CommRing} (f g : ring_hom R S) : is_ideal (coequalizer_ideal f g) := sorry

local attribute [instance] classical.prop_decidable

instance : has_coequalizers.{v+1 v} CommRing :=
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

instance : has_colimits.{v+1 v} CommRing := sorry

section
variables {J : Type v} [𝒥 : small_category J] [filtered.{v v} J]
include 𝒥

def matching (F : J ⥤ CommRing) (a b : Σ j : J, (F j).1) : Prop :=
∃ (j : J) (f_a : a.1 ⟶ j) (f_b : b.1 ⟶ j),
(F.map f_a).map a.2 = (F.map f_b).map b.2

def filtered_colimit (F : J ⥤ CommRing) :=
@quot (Σ j : J, (F j).1) (matching F)

local attribute [elab_with_expected_type] quot.lift

def filtered_colimit.zero (F : J ⥤ CommRing) : filtered_colimit F :=
quot.mk _ ⟨ filtered.default.{v v} J, 0 ⟩ 

-- TODO do this in two steps.
def filtered_colimit.add (F : J ⥤ CommRing) (x y : filtered_colimit F) : filtered_colimit F :=
quot.lift (λ p : Σ j, (F j).1, 
  quot.lift (λ q : Σ j, (F j).1, 
  quot.mk _ (begin 
    have s := filtered.obj_bound.{v v} p.1 q.1,
    exact ⟨ s.X, ((F.map s.ι₁).map p.2) + ((F.map s.ι₂).map q.2) ⟩
  end : Σ j, (F j).1))
  (λ q q' (r : matching F q q'), @quot.sound _ (matching F) _ _ 
    begin  
    dunfold matching,
    dsimp,
    dsimp [matching] at r,
    rcases r with ⟨j, f_a, f_b, e⟩,
    /- this is messy, but doable -/
    sorry
    end))
  (λ p p' (r : matching F p p'), funext $ λ q, begin dsimp, /- no idea -/ sorry end) x y

def filtered_colimit_is_comm_ring (F : J ⥤ CommRing) : comm_ring (filtered_colimit F) := 
{ add := filtered_colimit.add F,
  neg := sorry,
  mul := sorry,
  zero := filtered_colimit.zero F,
  one := sorry,
  add_comm := sorry,
  add_assoc := sorry,
  zero_add := sorry,
  add_zero := sorry,
  add_left_neg := sorry,
  mul_comm := sorry,
  mul_assoc := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry }

end

instance : has_filtered_colimits.{v+1 v} CommRing :=
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