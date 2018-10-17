import category_theory.limits

open category_theory

namespace category_theory.limits

universes u v

variables {J : Type v} [small_category J] {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variable {F : J ⥤ C}

def limit_cone_of_limit {t : cone F} (L : is_limit t) : is_terminal.{(max u v) v} t :=
{ lift := λ s, { hom := L.lift s, },
  uniq' := begin tidy, apply L.uniq, tidy, end } -- TODO uniq is marked @[back'], but the unifier fails to apply it

def limit_of_limit_cone {t : cone F} (L : is_terminal.{(max u v) v} t) : is_limit t :=
{ lift := λ s, (L.lift s).hom,
  uniq' := begin tidy, have p := L.uniq s { hom := m }, rw ← p, end }

def limits_are_limit_cones {t : cone F} : (is_limit t) ≅ (is_terminal.{(max u v) v} t) :=
{ hom := limit_cone_of_limit,
  inv := limit_of_limit_cone,
  hom_inv_id' := by obviously,
  inv_hom_id' := by obviously }

end category_theory.limits
