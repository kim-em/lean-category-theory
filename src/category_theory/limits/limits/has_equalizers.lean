import category_theory.limits.limits
import category_theory.limits.products
import category_theory.limits.equalizers
import category_theory.graph_category
import category_theory.discrete_category
-- import tactic.fin_cases

universes u v w

@[simp] lemma vector_nth_zero {α : Type u} {n : ℕ} (h : α) (t : list α) (p p'): @vector.nth α n ⟨h :: t, p⟩ ⟨0, p'⟩ = h := rfl

open category_theory

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables [has_limits.{u v} C] {J : Type v} [𝒥 : small_category J]
include 𝒥

instance : has_products.{u v} C :=
{ prod := λ β f, { .. (limit.cone (functor.of_function f)) },
  is_product := λ β f, { lift := λ s, limit.lift (functor.of_function f) { .. s } } }.

#print parallel_pair_functor._match_1

-- instance : has_equalizers.{u v} C :=
-- { equalizer := λ Y Z f g,
--     let c := limit.cone.{u v} (parallel_pair_functor f g) in
--     { X := c.X, ι := c.π  ⟨ ⟨ 0, by tidy ⟩ ⟩,
--       w' :=
--       begin
--         sorry
--         -- tidy,
--         -- have p₁ := @cone.w _ _ _ _ _ c ⟨ ⟨ 0, by tidy ⟩ ⟩ ⟨ ⟨ 1, by tidy ⟩ ⟩ p[ ⟨ ⟨ 0, by tidy ⟩ ⟩  ],
--         -- dsimp at p₁ {md:=semireducible},
--         -- repeat { erw category.comp_id at p₁ },
--         -- repeat { erw category.id_comp at p₁ },
--         -- erw p₁,
--         -- have p₂ := @cone.w _ _ _ _ _ c ⟨ ⟨ 0, by tidy ⟩ ⟩ ⟨ ⟨ 1, by tidy ⟩ ⟩ p[ ⟨ ⟨ 1, by tidy ⟩ ⟩  ],
--         -- dsimp at p₂ {md:=semireducible},
--         -- repeat { erw category.comp_id at p₂ },
--         -- repeat { erw category.id_comp at p₂ },
--         -- erw p₂,
--       end },
--   is_equalizer := λ Y Z f g,
--     let c := limit.cone.{u v} (parallel_pair_functor f g) in
--     { lift := λ s, limit.lift (parallel_pair_functor f g)
--       { X := s.X,
--         π := λ j, begin
--                     cases j, fin_cases,
--                     exact s.ι,
--                     refine s.ι ≫ f ≫ (eq_to_hom _), refl,
--                   end,
--         w' := begin
--                 tidy,
--                 fin_cases; fin_cases,
--                 tidy,
--                 cases f_1,
--                 tidy,
--                 sorry,
--                 fin_cases; fin_cases,
--                 dsimp [parallel_pair] at *,
--                 injection f_1_e_property,
--                 injection h_2,
--                 -- This is probably automatable, but it looks painful.
--               end, }, } }



end category_theory.limits