-- -- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import category_theory.universal.complete
-- import category_theory.walking
-- import tidy.transport

-- open category_theory
-- open category_theory.initial
-- open category_theory.walking

-- namespace category_theory.universal

-- universes u₁ v₁
-- variable {C : Type (u₁+1)}
-- variable [large_category C]

-- instance Limits_from_Products_and_Equalizers [has_Products.{u₁} C] [has_Equalizers.{u₁+1 u₁} C] : Complete C := {
--   limitCone := λ J _ F,
--     begin
--     resetI,
--     exact 
--     let product_over_objects   := product (λ j : J, F j) in
--     let product_over_morphisms := product (λ f : (Σ p : J × J, p.1 ⟶ p.2), F f.1.2) in 
--     let source    := product_over_morphisms.map (λ f, (product_over_objects.projection f.1.1) ≫ (F.map f.2))  in
--     let target    := product_over_morphisms.map (λ f, product_over_objects.projection f.1.2) in
--     let equalizer := equalizer source target in 
--     { obj     := 
--         { cone_point    := equalizer.equalizer,
--           cone_maps     := λ j : J, equalizer.inclusion ≫ (product_over_objects.projection j),
--           commutativity := λ j k f, begin
--                                      have p := congr_arg (λ i, i ≫ (product_over_morphisms.projection ⟨ (j, k), f⟩)) equalizer.witness,                                
--                                      tidy,
--                                     end
--      },
--      «from» := λ cone : Cone F, 
--         { cone_morphism := /- we need a morphism from the tip of f to the equalizer -/
--                          equalizer.map
--                            (product_over_objects.map (λ j, cone.cone_maps j)) (by obviously), } }
--    end
-- }

-- end category_theory.universal