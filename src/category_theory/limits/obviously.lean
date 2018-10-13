import category_theory.limits.terminal
import category_theory.limits.limits
import category_theory.tactics.obviously

open category_theory.limits

attribute [search] fork.w
attribute [search] cofork.w
attribute [search] square.w
attribute [search] cosquare.w
attribute [search] cone.w
attribute [search] cocone.w

attribute [search,elim] is_terminal.uniq
attribute [search,elim] is_initial.uniq

-- attribute [search] is_equalizer.fac
-- attribute [search,back'] is_equalizer.uniq

attribute [search] is_limit.fac
attribute [search,elim] is_limit.uniq
attribute [search] is_colimit.fac
attribute [search,elim] is_colimit.uniq

attribute [search] limit.pre_π limit.post_π colimit.ι_pre colimit.ι_post