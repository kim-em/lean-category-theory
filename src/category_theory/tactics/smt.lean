-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic
open smt_tactic
open lean.parser
open interactive

meta def unfold_coe : tactic unit := dunfold_target [ ``has_coe_to_fun.coe ]

meta def smt_simp   : tactic unit := using_smt $ intros >> try `[dsimp] >> try `[simp]
meta def smt_eblast : tactic unit := using_smt $ intros >> try `[dsimp] >> try unfold_coe >> try `[simp] >> eblast
meta def smt_ematch : tactic unit := using_smt $ intros >> smt_tactic.add_lemmas_from_facts >> try ematch