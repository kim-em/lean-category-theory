import category_theory.presheaves.sheaves
import category_theory.limits.preserves
import category_theory.functor.isomorphism

universes u v

open category_theory
open category_theory.limits
open category_theory.examples
open topological_space

-- We now provide an alternative 'pointwise' constructor for sheaves of types.

-- This should eventually be generalised to sheaves of categories with a
-- fibre functor with reflects iso and preserves limits.
section
variables {X : Top.{v}}

structure compatible_sections (c : cover X) (F : (opens X)ᵒᵖ ⥤ (Type u)) :=
  (sections      : Π i : c.I, F.obj (c.U i))
  (compatibility : Π i j : c.I, res_left i j F (sections i) = res_right i j F (sections j))

structure gluing {c : cover X} {F : (opens X)ᵒᵖ ⥤ (Type u)} (s : compatible_sections c F) :=
  («section»    : F.obj c.union)
  (restrictions : ∀ i : c.I, (F.map (c.sub i)) «section» = s.sections i)
  (uniqueness   : ∀ (Γ : F.obj c.union) (w : ∀ i : c.I, (F.map (c.sub i)) Γ = s.sections i), Γ = «section»)

-- definition sheaf.of_types
--   (presheaf        : (opens X)ᵒᵖ ⥤ (Type v))
--   (sheaf_condition : Π (c : cover X)
--                        (s : compatible_sections c presheaf), gluing s) :
--   sheaf.{v+1 v} X (Type v) :=
-- { presheaf := presheaf,
--   sheaf_condition := ⟨ λ c,
--   let σ : Π s : fork (left c presheaf) (right c presheaf), s.X → compatible_sections c presheaf :=
--     λ s x, { sections := λ i, pi.π (λ i : c.I, presheaf.obj (c.U i)) i (s.ι x),
--              compatibility := λ i j, congr_fun (congr_fun s.w x) (i,j), } in
--   { lift := λ s x, (sheaf_condition c (σ s x)).«section»,
--     fac'  := λ s, funext $ λ x, funext $ λ i, (sheaf_condition c (σ s x)).restrictions i,
--     uniq' := λ s m w, funext $ λ x, (sheaf_condition c (σ s x)).uniqueness (m x) (λ i, congr_fun (congr_fun w x) i),
--   } ⟩ }
end

section
variables {X : Top.{u}}

variables {V : Type (u+1)} [𝒱 : large_category V] [has_products.{u+1 u} V] (ℱ : V ⥤ (Type u))
          [faithful ℱ] [category_theory.limits.preserves_limits ℱ] [reflects_isos ℱ]
include 𝒱

-- This is a good project!
def sheaf.of_sheaf_of_types
  (presheaf : (opens X)ᵒᵖ ⥤ V)
  (underlying_is_sheaf : is_sheaf (presheaf ⋙ ℱ)) : is_sheaf presheaf := sorry

end
