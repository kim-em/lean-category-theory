-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import categories.examples.groups
import categories.universal.instances
import categories.universal.strongly_concrete

namespace category_theory.examples.groups

open category_theory
open category_theory.universal

universe u

instance : group punit := 
begin
  refine {
      one := punit.star,
      mul := λ x y, punit.star,
      ..
  },
  tidy,
end

-- private meta def unfold_is_group_hom := `[unfold is_group_hom]
-- local attribute [tidy] unfold_is_group_hom

instance maps_to_punit_hom {Z : Type u} [group Z] (f : Z → punit) : is_group_hom f := by obviously

instance Groups_has_TerminalObject : has_TerminalObject.{u+1 u} Group := {
  terminal_object := {
    obj := ⟨ punit, by obviously ⟩,
    «from» := by obviously
 }
}

variables {α : Type u} [group α] {β : Type u} [group β] {γ : Type u} [group γ] {δ : Type u} [group δ] 

-- instance group_binary_product : group (α × β) :=
-- begin
-- refine {
--   one := (1, 1),
--   mul := λ p q, (p.1 * q.1, p.2 * q.2),
--   inv := λ p, (p.1⁻¹, p.2⁻¹),
--   ..
-- },
-- tidy, -- PROJECT tidy is not (currently) the correct tool for this.
-- end

-- section
-- variables (f : α → β) [is_group_hom f] (g : γ → δ) [is_group_hom g]

-- def fun_prod : (α × γ) → (β × δ) := λ p, (f p.1, g p.2)

-- instance group_morphism_binary_product
--   : is_group_hom (fun_prod f g) := sorry

-- instance Groups_has_BinaryProducts : has_BinaryProducts Group := {
--   binary_product := λ s t, {
--     product             := ⟨ s.1 × t.1, by apply_instance ⟩ ,
--     left_projection     := ⟨ prod.fst ⟩,
--     right_projection    := ⟨ prod.snd ⟩,
--     map                 := λ _ f g, {
--       map := λ x, (f.map x, g.map x)
--    },
--     uniqueness          := λ _ f g w₁ w₂, begin
--                                              tidy,
--                                              have p := congr_arg semigroup_morphism.map w₁,
--                                              have p' := congr_fun p x,
--                                              exact p',
--                                              have q := congr_arg semigroup_morphism.map w₂,
--                                              have q' := congr_fun q x,
--                                              exact q',
--                                           end
--  }
-- }
-- end

-- definition group_product {I : Type u} {f : I → Type v} (s : Π i : I, group (f i)) : group (Π i, f i) := 
-- begin
-- refine {
--   one := λ i, 1,
--   mul := λ p q i, (p i) * (q i),
--   inv := λ p i, (p i)⁻¹,
--   .. 
-- },
-- sorry
-- end

-- definition group_morphism_product
--   {I : Type u}
--   {f g : I → Type v}
--   {s : Π i : I, group (f i)} {t : Π i : I, group (g i)} 
--   (f : Π i : I, semigroup_morphism (s i) (t i))
--   : semigroup_morphism (semigroup_product s) (semigroup_product t) := {
--   map := λ p i, (f i) (p i)
-- }

-- instance Groups_has_Products : has_Products Group := {
--   product := λ I F, {
--     product    := ⟨ _, semigroup_product (λ i, (F i).2) ⟩,
--     projection := λ i, {map := λ f, f i},
--     map        := λ _ f, {map := λ y j, (f j).map y},
--     uniqueness := λ _ f g w, begin
--                                tidy,   
--                                have p := congr_arg semigroup_morphism.map (w x_1),
--                                have p' := congr_fun p x,
--                                exact p',
--                              end
--  }
-- }

-- section
-- variables (f : α → β) [is_group_hom f] (g : α → β) [is_group_hom g]

-- definition group_equalizer := {x : α // f x = g x}

-- instance : group (group_equalizer f g) := 
-- begin
-- refine {
--   one := ⟨ 1, sorry ⟩,
--   mul := λ p q, ⟨ (p.val) * (q.val), by obviously ⟩,
--   inv := λ p, ⟨ (p.val)⁻¹, sorry ⟩,
--   .. 
-- },
-- sorry
-- end

-- instance Groups_has_Equalizers : has_Equalizers Group := {
--   equalizer := λ X Y f g, {
--     equalizer := ⟨ group_equalizer f.1 g.1, by apply_instance ⟩,
--     inclusion := {map := λ x, x.val},
--     map       := λ _ h w, {map := λ x, ⟨ h.map x, begin
--                                                     tidy, 
--                                                     have p := congr_arg semigroup_morphism.map w,
--                                                     have p' := congr_fun p x,
--                                                     exact p', 
--                                                   end ⟩},
--     uniqueness := λ r h k w, begin 
--                                tidy, 
--                                have p := congr_arg semigroup_morphism.map w,
--                                have p' := congr_fun p x,
--                                exact p'
--                              end,
--  }
-- }
-- end

end category_theory.examples.groups
