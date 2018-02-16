-- -- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison
-- import ..semigroups
-- import ...universal.instances
-- import ...universal.strongly_concrete

-- namespace categories.examples.semigroups

-- open categories

-- open categories.universal

-- @[applicable] lemma {u} punit_equality
--   (a b : punit.{u}): a = b := ♯

-- instance Semigroups_has_TerminalObject : has_TerminalObject CategoryOfSemigroups := {
--   terminal_object := {
--     terminal_object := ⟨ punit, trivial_semigroup ⟩,
--     morphism_to_terminal_object_from := ♯
--  }
-- }

-- local attribute [applicable] semigroup.mul_assoc

-- definition {u} semigroup_binary_product {α β : Type u} (s : semigroup α) (t: semigroup β) : semigroup (α × β) := {
--   mul := λ p q, (p.1 * q.1, p.2 * q.2),
--   mul_assoc := ♯
-- }

-- definition {u} semigroup_morphism_binary_product
--   {α β γ δ : Type u}
--   {s_f : semigroup α} {s_g: semigroup β} {t_f : semigroup γ} {t_g: semigroup δ}
--   (f : semigroup_morphism s_f t_f) (g : semigroup_morphism s_g t_g)
--   : semigroup_morphism (semigroup_binary_product s_f s_g) (semigroup_binary_product t_f t_g) := {
--   map := λ p, (f p.1, g p.2)
-- }

-- instance Semigroups_has_BinaryProducts : has_BinaryProducts CategoryOfSemigroups := {
--   binary_product := λ s t, {
--     product             := ⟨ _, semigroup_binary_product s.2 t.2 ⟩ ,
--     left_projection     := ⟨ prod.1 ⟩,
--     right_projection    := ⟨ prod.2 ⟩,
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

-- definition {u v} semigroup_product {I : Type u} {f : I → Type v} (s : Π i : I, semigroup (f i)) : semigroup (Π i, f i) := {
--   mul := λ p q i, (p i) * (q i),
--   mul_assoc := ♯
-- }

-- definition {u v} semigroup_morphism_product
--   {I : Type u}
--   {f g : I → Type v}
--   {s : Π i : I, semigroup (f i)} {t : Π i : I, semigroup (g i)} 
--   (f : Π i : I, semigroup_morphism (s i) (t i))
--   : semigroup_morphism (semigroup_product s) (semigroup_product t) := {
--   map := λ p i, (f i) (p i)
-- }

-- instance Semigroups_has_Products : has_Products CategoryOfSemigroups := {
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

-- definition {u} semigroup_equalizer {α β : Type u} {r : semigroup α} {s : semigroup β} (f g : semigroup_morphism r s) : semigroup {x : α // f.map x = g.map x} := {
--   mul := λ p q, ⟨ (p.val) * (q.val), ♯ ⟩ ,
--   mul_assoc := ♯
-- }

-- instance Semigroups_has_Equalizers : has_Equalizers CategoryOfSemigroups := {
--   equalizer := λ X Y f g, {
--     equalizer := ⟨ _, semigroup_equalizer f g ⟩,
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

-- end categories.examples.semigroups
