-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ...isomorphism
import ...natural_transformation
import ...equivalence
import ..comma_categories
import ..universal

open categories
open categories.functor
open categories.natural_transformation
open categories.isomorphism
open categories.equivalence
open categories.universal

namespace categories.universal

-- definition comma_Product_to_Product {C : Category} {I : Type} (F : I → C.Obj) (product : comma.Product F) : Product F := {
--     product       := product.terminal_object.1,
--     projection    := product.terminal_object.2.2.components,
--     map           := λ Z f, (product.morphism_to_terminal_object_from ⟨ Z, unit.star, ⟨ f ⟩ ⟩).val.1,
--     factorisation := begin
--                        have p := product.morphism_to_terminal_object_from,
--                        tidy,
--                      end,
--     uniqueness    := sorry
--}

-- definition Product_to_comma_Product {C : Category} {I : Type} (F : I → C.Obj) (product : Product F) : comma.Product F := sorry

-- definition Products_agree {C : Category} {I : Type} (F : I → C.Obj) : Isomorphism CategoryOfTypes (comma.Product f g) (Product f g) := sorry

-- PROJECT prove products are unique

end categories.universal