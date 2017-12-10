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

-- definition comma_Product_to_Product { C : Category } { I : Type } ( F : I → C.Obj ) ( product : comma.Product F ) : Product F := {
--     product       := product.object.1,
--     projection    := product.object.2.2.components,
--     -- Grah, "tactic failed, result contains meta-variables"
--     map           := λ Z f, (product.morphisms ⟨ Z, _, { components := f, naturality := begin intros, unfold_projections, unfold_projections_hypotheses, simp, induction f_1, induction down, induction down_1, simp, end } ⟩).val.1,
--     factorisation := sorry,
--     uniqueness    := sorry
-- }

-- definition Product_to_comma_Product { C : Category } { I : Type } ( F : I → C.Obj ) ( product : Product F ) : comma.Product F := sorry

-- definition Products_agree { C : Category } { I : Type } ( F : I → C.Obj ) : Isomorphism CategoryOfTypes (comma.Product f g) (Product f g) := sorry

-- PROJECT prove products are unique

end categories.universal