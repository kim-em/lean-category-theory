-- -- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import ...complete
-- import ...opposites
-- import categories.walking
-- import tidy.its

-- open categories
-- open categories.functor
-- open categories.natural_transformation
-- open categories.isomorphism
-- open categories.initial
-- open categories.walking
-- open categories.util.finite

-- namespace categories.universal

-- universes u₁ u₂ u₃

-- instance Limits_from_Products_and_Equalizers (C : Category.{u₁ u₂}) [has_Products.{u₁ u₂ u₃} C] [has_Equalizers.{u₁ u₂} C] : Complete.{u₁ u₂ u₃ u₃} C := {
--   limitCone := λ J F,
--     let product_over_objects   := product (F.onObjects) in
--     let product_over_morphisms := product (λ f : (Σ s : J.Obj, Σ t : J.Obj, J.Hom s t), F.onObjects f.2.1) in
--     let source    := product_over_morphisms.map (λ f, C.compose (product_over_objects.projection f.1) (F.onMorphisms f.2.2))  in
--     let target    := product_over_morphisms.map (λ f, product_over_objects.projection f.2.1) in
--     let equalizer := equalizer source target in {
--       terminal_object     := {
--         cone_point    := equalizer.equalizer,
--         cone_maps     := λ j : J.Obj, C.compose equalizer.inclusion (product_over_objects.projection j),
--         commutativity := λ j k f, begin
--                                    have p := congr_arg (λ i, C.compose i (product_over_morphisms.projection ⟨ j, ⟨ k, f ⟩ ⟩)) equalizer.witness,                                
--                                    tidy,
--                                   end
--      },
--       morphism_to_terminal_object_from := λ cone : Cone F, {
--         cone_morphism := /- we need a morphism from the tip of f to the equalizer -/
--                          equalizer.map
--                            (product_over_objects.map cone.cone_maps) ♯
--      }
--    }
-- }

-- end categories.universal