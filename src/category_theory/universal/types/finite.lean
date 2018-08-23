import category_theory.types.finite
import category_theory.universal.instances

open category_theory.universal

namespace category_theory.types

-- def {u} FiniteTypes_has_FiniteProducts : has_FiniteProducts CategoryOfFiniteTypes.{u} := {
--   product := λ I fin φ, {
--     product       := ⟨ (Π i : I, (φ i).1), sorry ⟩,
--     projection    := λ i x, x i,
--     map           := λ Z f z i, f i z, 
--     factorisation := by obviously,
--     uniqueness    := begin
--                        tidy,
--                        have p := witness x_1,
--                        tidy,
--                      end
--  }
--}

-- def {u} FiniteTypes_has_FiniteCoproducts : has_FiniteCoproducts CategoryOfFiniteTypes.{u} := {
--   coproduct := λ I fin φ, {
--     coproduct     := ⟨ (Σ i : I, (φ i).1), sorry ⟩, 
--     inclusion     := λ i x, ⟨ i, x ⟩ ,
--     map           := λ Z f p, f p.1 p.2, 
--     factorisation := by obviously,
--     uniqueness    := begin
--                        tidy,
--                        have p := witness fst,
--                        tidy,
--                      end
--  }
--}

-- def {u} FiniteTypes_has_Equalizers : has_Equalizers CategoryOfFiniteTypes.{u} :=
-- {equalizer := λ α _ f g,
--   {
--     equalizer     := ⟨ {x : α.1 // f x = g x}, sorry ⟩,
--     inclusion     := λ x, x.val,
--     witness       := by obviously,
--     map           := begin
--                        tidy,
--                        exact k a
--                        tidy,
--                     end,
--     factorisation := by obviously,
--     uniqueness    := by obviously
--  }
--}
-- attribute [instance] FiniteTypes_has_Equalizers

end category_theory.types