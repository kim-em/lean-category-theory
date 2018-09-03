import .limits
import .colimits

open category_theory

universes u v

namespace category_theory.universal

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

structure is_zero (t : C) :=
(lift : ∀ (s : C), s ⟶ t)
(uniq_lift : ∀ (s : C) (m : s ⟶ t), m = lift s . obviously)
(desc : ∀ (s : C), t ⟶ s)
(uniq_desc : ∀ (s : C) (m : t ⟶ s), m = desc s . obviously)

namespace is_zero
def to_is_initial  {t : C} (Z : is_zero.{u v} t) : is_initial.{u v} t  := { desc := Z.desc, uniq := Z.uniq_desc }
def to_is_terminal {t : C} (Z : is_zero.{u v} t) : is_terminal.{u v} t := { lift := Z.lift, uniq' := Z.uniq_lift }
end is_zero


restate_axiom is_zero.uniq_lift
restate_axiom is_zero.uniq_desc
attribute [search, back'] is_zero.uniq_lift_lemma is_zero.uniq_desc_lemma

@[extensionality] lemma is_zero.ext {X : C} (P Q : is_zero.{u v} X) : P = Q := 
begin cases P, cases Q, obviously, end

-- instance hom_to_zero_subsingleton (X Z : C) (B : is_zero.{u v} Z) : subsingleton (X ⟶ Z) :=
-- universal.hom_to_terminal_subsingleton X Z B.to_is_terminal
-- instance hom_from_zero_subsingleton (Z X : C) (B : is_zero.{u v} Z) : subsingleton (Z ⟶ X) :=
-- universal.hom_to_initial_subsingleton Z X B.to_is_initial

variable (C)

class has_zero_object :=
(zero : C)
(is : is_zero.{u v} zero)

end category_theory.universal

namespace category_theory.universal

def zero_object  := has_zero_object.zero.{u v}

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables [has_zero_object.{u v} C]

def zero_morphism (X Y : C) : X ⟶ Y := ((has_zero_object.is.{u v} C).lift X) ≫ ((has_zero_object.is.{u v} C).desc Y)

instance hom_has_zero (X Y : C) : _root_.has_zero (X ⟶ Y) := { zero := zero_morphism X Y }

@[simp] lemma zero_morphism_left  {X Y Z : C} (f : Y ⟶ Z) : (zero_morphism X Y) ≫ f = zero_morphism X Z :=
begin
  unfold zero_morphism,
  rw category.assoc,
  congr,
  sorry
end
@[simp] lemma zero_morphism_right {X Y Z : C} (f : X ⟶ Y) : f ≫ (zero_morphism Y Z) = zero_morphism X Z :=  
begin
  unfold zero_morphism,
  rw ← category.assoc,
  congr,
  sorry
end

end category_theory.universal

