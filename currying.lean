-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .equivalence
import .products.products

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor
open tqft.categories.equivalence

namespace tqft.categories.natural_transformation

-- PROJECT show Fun(C → Fun(D → E)) is equivalent to Fun(C × D → E)

theorem {u1 v1 u2 v2 u3 v3} Currying_for_functors
  ( C : Category.{u1 v1} )
  ( D : Category.{u2 v2} )
  ( E : Category.{u3 v3} ) :
  Equivalence (FunctorCategory C (FunctorCategory D E)) (FunctorCategory (C × D) E) :=
  begin
    fsplit,
    fsplit,
    dunfold_everything,
    -- FIXME
    -- I'd really like a satisfactory answer to https://groups.google.com/d/msg/lean-user/6Du2cNKwURs/Z9D4fYNVAwAJ
    -- before proceeding here.
  end

  -- {
  --   functor := {
  --     onObjects     := λ F, {
  --       onObjects     := λ p, (F.onObjects p.1).onObjects p.2,
  --       onMorphisms   := sorry,
  --       identities    := sorry,
  --       functoriality := sorry
  --     },
  --     onMorphisms   := sorry,
  --     identities    := sorry,
  --     functoriality := sorry
  --   },
  --   inverse := sorry,
  --   isomorphism_1 := sorry,
  --   isomorphism_2 := sorry
  -- }

end tqft.categories.natural_transformation