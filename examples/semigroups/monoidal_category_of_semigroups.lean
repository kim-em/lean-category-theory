-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...monoidal_categories.braided_monoidal_category
import .semigroups

open tqft.categories.natural_transformation

namespace tqft.categories.examples.semigroups

open tqft.categories.monoidal_category

-- definition {u} semigroup_product { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) : semigroup (α × β) := {
--   mul := λ p q, (p.fst * q.fst, p.snd * q.snd),
--   -- From https://groups.google.com/d/msg/lean-user/bVs5FdjClp4/cbDZOqq_BAAJ
--   mul_assoc := begin 
--                 abstract {
--                   intros,
--                   admit,
--                 }
--               end
-- }

set_option pp.all true

-- definition {u} semigroup_morphism_product
--   { α β γ δ : Type u }
--   { s_f : semigroup α } { s_g: semigroup β } { t_f : semigroup γ } { t_g: semigroup δ }
--   ( f : semigroup_morphism s_f t_f ) ( g : semigroup_morphism s_g t_g )
--   : semigroup_morphism (semigroup_product s_f s_g) (semigroup_product t_f t_g) := {
--   map := λ p, (f p.1, g p.2),
--   multiplicative :=
--     begin
--       -- cf https://groups.google.com/d/msg/lean-user/bVs5FdjClp4/tfHiVjLIBAAJ
--       abstract {
--         tidy,
--         admit,
--         admit
--       }
--     end
-- }

-- PROJECT really this should be a special case of the (uniquely braided, symmetric) monoidal structure coming from a product.

-- open tqft.categories.products

-- definition TensorProduct_for_Semigroups : TensorProduct CategoryOfSemigroups := {
--     onObjects     := λ p, ⟨ p.1.1 × p.2.1, semigroup_product p.1.2 p.2.2 ⟩,
--     onMorphisms   := λ s t f, semigroup_morphism_product f.1 f.2,
--     identities    := ♯,
--     functoriality := ♮
--   }

-- -- FIXME (on edulis) chain is running off the end here
-- definition Associator_for_Semigroups : Associator TensorProduct_for_Semigroups := {
--     morphism := {
--       components := λ _, {
--         map := λ t, (t.1.1, (t.1.2, t.2)),
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     inverse := {
--       components := λ _, {
--         map := λ t, ((t.1, t.2.1), t.2.2),
--         multiplicative := ♮
--       },
--       naturality := ♮  
--     },
--     witness_1 := ♯,
--     witness_2 := ♯
--   }

-- definition TensorUnit_for_Semigroups : CategoryOfSemigroups.Obj := ⟨ punit, trivial_semigroup ⟩  -- punit is just a universe-parameterized version of unit

-- definition LeftUnitor_for_Semigroups : @LeftUnitor CategoryOfSemigroups TensorUnit_for_Semigroups TensorProduct_for_Semigroups := {
--     morphism := {
--       components := λ _, {
--         map := λ t, t.2,
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     inverse := {
--       components := λ _, {
--         map := λ t, (punit.star, t),
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     witness_1 := ♯,
--     witness_2 := ♮
--   }

-- definition RightUnitor_for_Semigroups : @RightUnitor CategoryOfSemigroups TensorUnit_for_Semigroups TensorProduct_for_Semigroups := {
--     morphism := {
--       components := λ _, {
--         map := λ t, t.1,
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     inverse := {
--       components := λ _, {
--         map := λ t, (t, punit.star),
--         multiplicative := ♮
--       },
--       naturality := ♮ 
--     },
--     witness_1 := ♯,
--     witness_2 := ♮
--   }

-- definition MonoidalStructureOnCategoryOfSemigroups : MonoidalStructure CategoryOfSemigroups := {
--   tensor := TensorProduct_for_Semigroups,
--   tensor_unit := TensorUnit_for_Semigroups,
--   associator_transformation := Associator_for_Semigroups,
--   left_unitor := LeftUnitor_for_Semigroups,
--   right_unitor := RightUnitor_for_Semigroups,
--   pentagon := ♯,
--   triangle := ♯
-- }

-- open tqft.categories.natural_transformation
-- open tqft.categories.braided_monoidal_category

-- Commented out while I work on an alternative.
-- definition SymmetryOnCategoryOfSemigroups : Symmetry MonoidalStructureOnCategoryOfSemigroups := {
--   braiding             := {
--     morphism  := {
--       components := λ _, {
--                            map := λ p, (p.2, p.1),
--                            multiplicative := ♮
--                          },
--       naturality := ♮
--     },
--     inverse   := {
--       components := λ _, {
--                            map := λ p, (p.2, p.1), -- PROJECT this is sufficiently obvious that automation should be doing it for us!
--                            multiplicative := ♮
--                          },
--       naturality := ♮
--     },
--     witness_1 := ♯,
--     witness_2 := ♯
--   },
--   hexagon_1 := ♯,
--   hexagon_2 := ♯,
--   symmetry  := ♮
-- }

end tqft.categories.examples.semigroups
