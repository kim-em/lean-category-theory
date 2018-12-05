import category_theory.natural_isomorphism
import category_theory.products
import category_theory.types
import category_theory.fully_faithful
import category_theory.yoneda
import category_theory.limits.cones
import category_theory.equivalence

import tidy.tidy

open category_theory

@[suggest] def use_category_theory := `category_theory

attribute [elim] full.preimage
attribute [forward] faithful.injectivity

attribute [search] yoneda.obj_map_id

attribute [search] equivalence.fun_inv_map equivalence.inv_fun_map 
                   is_equivalence.fun_inv_map is_equivalence.inv_fun_map

-- attribute [search] cone_morphism.w cocone_morphism.w