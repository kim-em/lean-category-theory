-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import tidy.applicable tidy.force tidy.at_least_one tidy.repeat_at_least_once tidy.smt tidy.tidy

import tidy.auto_cast

open tactic

meta def tidy' : tactic unit := tidy -- getting rid of the optional paramater

@[applicable] lemma {u v} pairs_componentwise_equal {α : Type u} {β : Type v} {X Y : α × β} (p1 : X.1 = Y.1) (p2 : X.2 = Y.2) : X = Y := ♯

meta def trace_goal_type : tactic unit :=
do g ← target,
   tactic.trace g,
   infer_type g >>= tactic.trace,
   tactic.skip

set_option formatter.hide_full_terms false

set_option pp.proofs false