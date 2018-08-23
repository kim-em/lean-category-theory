-- -- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import category_theory.isomorphism
-- import category_theory.natural_transformation
-- import category_theory.equivalence
-- import category_theory.universal.comma_categories
-- import category_theory.universal

-- open categories
-- open categories.functor
-- open categories.isomorphism
-- open categories.equivalence
-- open categories.universal

-- namespace categories.universal

-- -- def comma_Product_to_Product {C : Category} {I : Type} (F : I → C.Obj) (product : comma.Product F) : Product F := {
-- --     product       := product.terminal_object.1,
-- --     projection    := product.terminal_object.2.2.components,
-- --     map           := λ Z f, (product.morphism_to_terminal_object_from ⟨ Z, unit.star, ⟨ f ⟩ ⟩).val.1,
-- --     factorisation := begin
-- --                        have p := product.morphism_to_terminal_object_from,
-- --                        tidy,
-- --                      end,
-- --     uniqueness    := sorry
-- --}

-- -- def Product_to_comma_Product {C : Category} {I : Type} (F : I → C.Obj) (product : Product F) : comma.Product F := sorry

-- -- def Products_agree {C : Category} {I : Type} (F : I → C.Obj) : Isomorphism CategoryOfTypes (comma.Product f g) (Product f g) := sorry

-- -- PROJECT prove products are unique

-- end categories.universal