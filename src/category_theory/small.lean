/- Categories which are small relative to a cardinal κ.
   κ-filtered categories.
   Normally we care about these concepts for categories which are
   used to index (co)limits, so we work with small_categories. -/

import category_theory.category
import category_theory.functor
import category_theory.limits.shape -- for cocone
import set_theory.cardinal

universe u

namespace category_theory

variables (κ : cardinal.{u})

def is_kappa_small (I : Type u) [small_category.{u} I] : Prop :=
cardinal.mk (Σ (a b : I), a ⟶ b) < κ

structure kappa_filtered (C : Type u) [small_category.{u} C] : Prop :=
(has_cocones : ∀ (I : Type u) [small_category.{u} I] (hI : is_kappa_small κ I) (F : I ⥤ C),
  nonempty (limits.cocone F))

end category_theory
