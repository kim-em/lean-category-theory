import category_theory.natural_isomorphism
import category_theory.products
import category_theory.types
import category_theory.embedding
import category_theory.yoneda
import category_theory.limits.cones

import tidy.tidy

open category_theory

attribute [search] category.id_comp category.comp_id category.assoc
attribute [search] category_theory.functor.map_id category_theory.functor.map_comp
attribute [search] nat_trans.naturality nat_trans.vcomp_app nat_trans.vcomp_assoc nat_trans.hcomp_app nat_trans.exchange
attribute [search] prod_id prod_comp functor.prod_obj functor.prod_map nat_trans.prod_app
attribute [search] functor.category.id_app functor.category.comp_app functor.category.nat_trans.app_naturality functor.category.nat_trans.naturality_app
attribute [search] functor_to_types.map_comp functor_to_types.map_id functor_to_types.naturality
attribute [search] iso.hom_inv_id iso.inv_hom_id is_iso.hom_inv_id is_iso.inv_hom_id

attribute [search] nat_iso.comp_app nat_iso.naturality_1 nat_iso.naturality_2

attribute [elim] full.preimage
attribute [search] full.witness functor.image_preimage
attribute [forward] faithful.injectivity

attribute [search] yoneda.obj_map_id

-- attribute [search] cone_morphism.w cocone_morphism.w