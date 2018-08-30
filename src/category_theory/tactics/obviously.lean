import category_theory.functor_category
import category_theory.natural_transformation
import category_theory.products
import category_theory.types
import tidy.tidy

open category_theory

attribute [ematch] category.id_comp category.comp_id category.assoc
attribute [ematch] category_theory.functor.map_id category_theory.functor.map_comp
attribute [ematch] nat_trans.naturality nat_trans.vcomp_app nat_trans.vcomp_assoc nat_trans.hcomp_app nat_trans.exchange
attribute [ematch] prod_id prod_comp functor.prod_obj functor.prod_map nat_trans.prod_app
attribute [ematch] functor.category.id_app functor.category.comp_app functor.category.nat_trans.app_naturality functor.category.nat_trans.naturality_app 
attribute [ematch] functor_to_types.map_comp functor_to_types.map_id functor_to_types.naturality
