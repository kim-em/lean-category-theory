import category_theory.limits.limits
import category_theory.limits.binary_products
import category_theory.limits.products
import category_theory.limits.pullbacks
import category_theory.limits.equalizers
import category_theory.tactics.obviously

open category_theory.limits

attribute [search] fork.condition cofork.condition square.condition cosquare.condition cone.w cocone.w

attribute [search] is_limit.fac
attribute [search,elim] is_limit.uniq
attribute [search] is_colimit.fac
attribute [search,elim] is_colimit.uniq

attribute [search] limit.pre_π limit.post_π colimit.ι_pre colimit.ι_post

-- attribute [search] is_binary_product.fac₁ is_binary_product.fac₂
-- attribute [search,elim] is_binary_product.uniq

-- attribute [search] prod.lift_π₁ prod.lift_π₂ prod.map_π₁ prod.map_π₂ prod.swap_π₁ prod.swap_π₂
-- attribute [search] coprod.ι₁_desc coprod.ι₂_desc coprod.ι₁_map coprod.ι₂_map coprod.ι₁_swap coprod.ι₂_swap

-- attribute [search] prod.swap_swap prod.lift_swap prod.swap_map prod.map_map
-- attribute [search] coprod.swap_swap coprod.swap_desc coprod.swap_map coprod.map_map

-- attribute [search] is_product.fac is_coproduct.fac
-- attribute [search,elim] is_product.uniq is_coproduct.uniq

attribute [search] pi.lift_π pi.map_π pi.pre_π pi.post_π
attribute [search] sigma.ι_desc sigma.ι_map sigma.ι_pre sigma.ι_post

-- attribute [search] is_pullback.fac₁ is_pullback.fac₂
-- attribute [search,elim] is_pullback.uniq
-- attribute [search] is_pushout.fac₁ is_pushout.fac₂
-- attribute [search,elim] is_pushout.uniq

-- attribute [search] is_equalizer.fac
-- attribute [search,elim] is_equalizer.uniq
-- attribute [search] is_coequalizer.fac
-- attribute [search,elim] is_coequalizer.uniq
