import categories.currying

namespace category_theory

universes u₁ u₂ v₂ 

variables (C : Type u₁) [small_category C] (D : Type u₁) [small_category D] (E : Type u₂) [ℰ : category.{u₂ v₂} E]
include ℰ

local attribute [back] category.id -- this is usually a bad idea, but just what we needed here

def currying : Equivalence (C ↝ (D ↝ E)) ((C × D) ↝ E) := 
{ functor := uncurry C D E,
  inverse := curry C D E,
  isomorphism_1 := 
  { hom := { app := λ X, { app := λ Y, { 
      app := by obviously, 
      naturality := begin 
                     tidy, 
                    --  erw [category.assoc_lemma, category.comp_id_lemma, functor.map_id_lemma], refl,
                     -- 12/6/3 (old) vs 192/128/13 (new)
                     (do tactic.interactive.rewrite_search_using [`ematch] {trace_summary := tt} >>= tactic.trace)
                    end },
    naturality := sorry }, naturality := sorry },
    inv := sorry,
    hom_inv_id := sorry,
    inv_hom_id := sorry },
  isomorphism_2 := sorry }


set_option pp.proofs true
#print currying._proof_1