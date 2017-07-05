-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

meta def if_then_else { α : Type } ( i : tactic unit ) ( t e : tactic α ) : tactic α :=
do r ← (i >> pure tt) <|> pure ff,
   if r then do t else do e
   
meta def dependent_if_then_else { α β : Type } ( i : tactic α ) ( t : α → tactic β ) ( e : tactic β ) : tactic β :=
do r ← tactic.try_core i,
   match r with
   | some a := t a
   | none   := e
   end