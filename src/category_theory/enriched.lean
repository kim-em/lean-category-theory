import category_theory.limits
import category_theory.universal.continuous
import category_theory.limits.types
import category_theory.embedding

open category_theory.limits

universes u v

namespace category_theory

variables {C : Type u} [𝒞 : category.{u v} C]
variables (V : Type (v+1)) [𝒱 : large_category V]
          [has_terminal_object.{v+1 v} V] [has_binary_products.{v+1 v} V]
          (ℱ : V ⥤ Type v) [faithful ℱ] [continuous ℱ]

include 𝒞 𝒱

class enriched_over :=
(enriched_hom : C → C → V)
(enriched_id : Π {X : C}, terminal V ⟶ enriched_hom X X)
(enriched_comp : Π {X Y Z : C}, prod (enriched_hom X Y) (enriched_hom Y Z) ⟶ enriched_hom X Z)
(fibre_hom : Π {X Y : C}, ℱ (enriched_hom X Y) ≅ (X ⟶ Y))
/- to state compatibility between enriched_comp and comp, we need that the fibre functor preserves limits -/

-- TODO simple examples

/-- The category of types is enriched over itself. -/
instance : enriched_over.{u v} (Type v) (functor.id _) :=
{ enriched_hom := λ X Y, X ⟶ Y,
  enriched_id := λ (X : C) _, 𝟙 X,
  enriched_comp := λ X Y Z, begin dsimp, exact λ p, p.1 ≫ p.2, end,
  fibre_hom := by obviously }


end category_theory