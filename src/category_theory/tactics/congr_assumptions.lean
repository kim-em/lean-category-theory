-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

open tactic.interactive

private meta def exact_symm ( e : expr ) : tactic string := 
do 
   exact ``((%%e).symm),
   pure ("exact (" ++ e.to_string ++ ".symm)")

private meta def exact_congr_fun_expr ( e f : expr ) : tactic string := 
do 
   exact ``(congr_fun %%e %%f),
   pure ("exact (congr_fun " ++ e.to_string ++ " " ++ f.to_string ++ ")")

private meta def exact_congr_arg_expr ( e f : expr ) : tactic string := 
do 
   exact ``(congr_arg %%e %%f),
   pure ("exact (congr_arg " ++ e.to_string ++ " " ++ f.to_string ++ ")")

-- TODO I think these may be slow...
meta def congr_assumptions : tactic string :=
do l ← local_context,
   first(l.for(λ h, exact_symm h))
   <|> first(l.for(λ h1, first (l.for(λ h2, exact_congr_fun_expr h1 h2))))
   <|> first(l.for(λ h1, first (l.for(λ h2, exact_congr_arg_expr h1 h2))))
