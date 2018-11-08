import category_theory.functor_category
import category_theory.products
import category_theory.tactics.obviously
import tactic.interactive

universes u₁ v₁

open category_theory

def functor.prod' (C : Type u₁) [category.{u₁ v₁} C] : ( (C ⥤ C) × (C ⥤ C) ) ⥤ (C ⥤ C) :=
begin
  refine
  { obj := λ a, a.1 ⋙ a.2, map' := λ a b f, f.1 ◫ f.2,
    map_comp' := _ },
  tidy,
    -- Z_fst Z_snd Y_fst Y_snd : C ⥤ C,
    -- g_fst : Y_fst ⟶ Z_fst,
    -- g_snd : Y_snd ⟶ Z_snd,
    -- X_fst X_snd : C ⥤ C,
    -- f_fst : X_fst ⟶ Y_fst,
    -- f_snd : X_snd ⟶ Y_snd
    -- ⊢ ⇑f_snd (⇑X_fst X_1) ≫
    --       ⇑g_snd (⇑X_fst X_1) ≫ functor.map Z_snd (⇑f_fst X_1) ≫ functor.map Z_snd (⇑g_fst X_1) =
    --     ⇑f_snd (⇑X_fst X_1) ≫
    --       functor.map Y_snd (⇑f_fst X_1) ≫ ⇑g_snd (⇑Y_fst X_1) ≫ functor.map Z_snd (⇑g_fst X_1)
conv_lhs { congr, skip, erw [←category.assoc] },
conv_lhs { congr, skip, congr, erw [←nat_trans.naturality] },
conv_rhs { congr, skip, erw [←category.assoc] }

end