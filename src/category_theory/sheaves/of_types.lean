import category_theory.sheaves
import category_theory.universal.continuous
import category_theory.functor.isomorphism

universes u v

open category_theory
open category_theory.universal
open category_theory.examples.topological_spaces

-- We now provide an alternative 'pointwise' constructor for sheaves of types.

-- This should eventually be generalised to sheaves of categories with a
-- fibre functor with reflects iso and preserves limits.
section
variables {α : Type v} [topological_space α]

structure compatible_sections (cover : cover' α) (F : presheaf (open_set α) (Type u)) := 
  (sections      : Π i : cover.I, F.obj (cover.U i))
  (compatibility : Π i j : cover.I, res_left i j F (sections i) = res_right i j F (sections j))

structure gluing {cover : cover' α} {F : presheaf (open_set α) (Type u)} (s : compatible_sections cover F) :=
  («section»    : F.obj cover.union)
  (restrictions : ∀ i : cover.I, (F.map (cover.union_subset i)) «section» = s.sections i)
  (uniqueness   : ∀ (Γ : F.obj cover.union) (w : ∀ i : cover.I, (F.map (cover.union_subset i)) Γ = s.sections i), Γ = «section»)

definition sheaf.of_types
  (presheaf        : presheaf (open_set α) (Type v))
  (sheaf_condition : Π (cover : cover' α) 
                        (s : compatible_sections cover presheaf), gluing s) :
  sheaf.{v+1 v} α (Type v) :=
{ presheaf := presheaf,
  sheaf_condition := ⟨ λ c,
  let σ : Π s : fork (left c presheaf) (right c presheaf), s.X → compatible_sections c presheaf :=
    λ s x, { sections := λ i, select_section c presheaf i (s.ι x),
             compatibility := λ i j, congr_fun (congr_fun s.w x) (i,j), } in
  { lift := λ s x, (sheaf_condition c (σ s x)).«section»,
    fac  := λ s, funext $ λ x, funext $ λ i, (sheaf_condition c (σ s x)).restrictions i,
    uniq := λ s m w, funext $ λ x, (sheaf_condition c (σ s x)).uniqueness (m x) (λ i, congr_fun (congr_fun w x) i), 
  } ⟩ }
end

section
variables {α : Type u} [topological_space α]

variables {V : Type (u+1)} [𝒱 : large_category V] [has_products.{u+1 u} V] (ℱ : V ⥤ (Type u)) 
          [faithful ℱ] [category_theory.universal.continuous ℱ] [reflects_isos ℱ]
include 𝒱

-- This is a good project!
def sheaf.of_sheaf_of_types
  (presheaf : presheaf (open_set α) V)
  (underlying_is_sheaf : is_sheaf (presheaf ⋙ ℱ)) : is_sheaf presheaf := sorry

end
