import category_theory.limits.terminal
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