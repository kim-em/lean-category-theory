-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import ...monoidal_categories.braided_monoidal_category
import .semigroups

open tqft.categories.natural_transformation

namespace tqft.categories.examples.semigroups

universe variables u

open tqft.categories.monoidal_category

@[reducible] definition semigroup_product { α β : Type u } ( s : semigroup α ) ( t: semigroup β ) : semigroup (α × β) := {
  mul := λ p q, (p.fst * q.fst, p.snd * q.snd),
  -- From https://groups.google.com/d/msg/lean-user/bVs5FdjClp4/cbDZOqq_BAAJ
  mul_assoc := begin 
                abstract {
                  intros,
                  simp [@mul.equations._eqn_1 (α × β)]
                }
              end
}

@[reducible] definition semigroup_morphism_product
  { α β γ δ : Type u }
  { s_f : semigroup α } { s_g: semigroup β } { t_f : semigroup γ } { t_g: semigroup δ }
  ( f : semigroup_morphism s_f t_f ) ( g : semigroup_morphism s_g t_g )
  : semigroup_morphism (semigroup_product s_f s_g) (semigroup_product t_f t_g) := {
  map := λ p, (f p.1, g p.2),
  multiplicative :=
    begin
      -- cf https://groups.google.com/d/msg/lean-user/bVs5FdjClp4/tfHiVjLIBAAJ
      abstract {
        intros,
        unfold mul has_mul.mul,
        dsimp,
        simp
      }
    end
}

open tqft.categories.products

-- set_option trace.dsimplify true
-- set_option trace.debug.dsimplify true

definition TensorProduct_for_Semigroups : TensorProduct CategoryOfSemigroups := {
    onObjects     := λ p, ⟨ p.1.1 × p.2.1, semigroup_product p.1.2 p.2.2 ⟩,
    onMorphisms   := λ s t f, semigroup_morphism_product f.1 f.2,
    identities    := ♯,
    functoriality := ♮
  }

definition Associator_for_Semigroups : Associator TensorProduct_for_Semigroups := {
    morphism := {
      components := λ _, {
        map := λ t, (t.1.1, (t.1.2, t.2)),
        multiplicative := ♮
      },
      naturality := ♮ 
    },
    inverse := {
      components := λ _, {
        map := λ t, ((t.1, t.2.1), t.2.2),
        multiplicative := ♮
      },
      naturality := ♮  
    },
    witness_1 := ♯,
    witness_2 := ♯
  }

definition TensorUnit_for_Semigroups : CategoryOfSemigroups.Obj := ⟨ punit, trivial_semigroup ⟩

definition LeftUnitor_for_Semigroups : @LeftUnitor CategoryOfSemigroups TensorUnit_for_Semigroups TensorProduct_for_Semigroups := {
    morphism := {
      components := λ _, {
        map := λ t, t.2,
        multiplicative := ♮
      },
      naturality := ♮ 
    },
    inverse := {
      components := λ _, {
        map := λ t, (punit.star, t),
        multiplicative := ♮
      },
      naturality := ♮ 
    },
    witness_1 := ♯,
    witness_2 := ♮
  }

definition RightUnitor_for_Semigroups : @RightUnitor CategoryOfSemigroups TensorUnit_for_Semigroups TensorProduct_for_Semigroups := {
    morphism := {
      components := λ _, {
        map := λ t, t.1,
        multiplicative := ♮
      },
      naturality := ♮ 
    },
    inverse := {
      components := λ _, {
        map := λ t, (t, punit.star),
        multiplicative := ♮
      },
      naturality := ♮ 
    },
    witness_1 := ♯,
    witness_2 := ♮
  }

@[unfoldable] definition MonoidalStructureOnCategoryOfSemigroups : MonoidalStructure CategoryOfSemigroups := {
  tensor := TensorProduct_for_Semigroups,
  tensor_unit := TensorUnit_for_Semigroups, -- punit is just a universe-parameterized version of unit
  associator_transformation := Associator_for_Semigroups,
  left_unitor := LeftUnitor_for_Semigroups,
  right_unitor := RightUnitor_for_Semigroups,
  pentagon := ♯,
  triangle := ♯
}

open tqft.categories.natural_transformation
open tqft.categories.braided_monoidal_category

@[unfoldable] definition SymmetryOnCategoryOfSemigroups : Symmetry MonoidalStructureOnCategoryOfSemigroups := {
  braiding             := {
    morphism  := {
      components := λ _, {
                           map := λ p, (p.2, p.1),
                           multiplicative := ♮
                         },
      naturality := ♮
    },
    inverse   := {
      components := λ _, {
                           map := λ p, (p.2, p.1), -- PROJECT this is sufficiently obvious that automation should be doing it for us!
                           multiplicative := ♮
                         },
      naturality := ♮
    },
    witness_1 := ♮,
    witness_2 := ♮
  },
  hexagon_1 := ♮,
  hexagon_2 := ♮,
  symmetry  := ♮
}

end tqft.categories.examples.semigroups
