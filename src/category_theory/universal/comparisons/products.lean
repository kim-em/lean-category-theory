-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ...isomorphism
import ...natural_transformation
import ...equivalence
import ..comma_categories
import ..universal

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation
open tqft.categories.isomorphism
open tqft.categories.equivalence
open tqft.categories.universal

namespace tqft.categories.universal

-- definition comma_Product_to_Product { C : Category } { I : Type } ( F : I → C.Obj ) ( product : comma.Product F ) : Product F := {
--     product       := product.object.1,
--     projection    := product.object.2.2.components,
--     map           := sorry,
--     factorisation := sorry,
--     uniqueness    := sorry
-- }

-- definition Product_to_comma_Product { C : Category } { I : Type } ( F : I → C.Obj ) ( product : Product F ) : comma.Product F := sorry

-- definition Products_agree { C : Category } { I : Type } ( F : I → C.Obj ) : Isomorphism CategoryOfTypes (comma.Product f g) (Product f g) := sorry

-- PROJECT prove products are unique

end tqft.categories.universal