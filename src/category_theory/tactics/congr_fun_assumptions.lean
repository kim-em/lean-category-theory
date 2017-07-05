-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

namespace tactic.interactive

private meta def exact_congr_fun_expr ( e f : expr ) : tactic string := 
do -- trace ("attempting exact_congr_fun_expr with " ++ e.to_string ++ " " ++ f.to_string),
   exact ``(congr_fun %%e %%f),
   pure ("exact (congr_fun " ++ e.to_string ++ " " ++ f.to_string ++ ")")

meta def congr_fun_assumptions : tactic string :=
do l ← local_context,
   result ← first(l.for(λ h1, first (l.for(λ h2, exact_congr_fun_expr h1 h2)))),
   pure (result ++ " -- or 'congr_fun_assumptions'")

end tactic.interactive