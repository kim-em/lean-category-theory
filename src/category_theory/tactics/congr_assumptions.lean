-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

open tactic.interactive

private meta def is_equation ( e : expr ) := e.is_eq.is_some

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
do t ← target,
   guard (is_equation t),
   l ← local_context,
   first(l.for(λ h, infer_type h >>= λ t, guard (is_equation t) >> exact_symm h))
   <|> first(l.for(λ h1, infer_type h1 >>= λ t, guard (is_equation t) >> first (l.for(λ h2, exact_congr_fun_expr h1 h2))))
   <|> first(l.for(λ h1, infer_type h1 >>= λ t, guard (is_equation t) >> first (l.for(λ h2, exact_congr_arg_expr h2 h1))))

lemma test1 (f : nat → nat) (x y : nat) (p : x = y) : f x = f y :=
begin 
  congr_assumptions
end
lemma test2 (f g: nat → nat) (x : nat) (p : f = g) : f x = g x :=
begin 
  congr_assumptions
end
lemma test3 (x y: nat) (p : x = y) : y = x :=
begin
  congr_assumptions
end
lemma test4 (x: nat) (f g : nat → nat) (p : (λ (x : nat), f (g x)) = id) : f(g x) = x :=
begin
  congr_assumptions
end
