-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .if_then_else

open tactic
open nat

private meta structure chain_progress { α : Type } :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (tactic α) )

structure chain_cfg := 
  ( max_steps   : nat  := 500 )
  ( trace_steps : bool := ff )

private meta def chain' { α : Type } [ has_to_format α ] ( cfg : chain_cfg ) ( tactics : list (tactic α) ) : chain_progress → tactic (list α)
| ⟨ 0,      results, _ ⟩       := trace (format!"... chain tactic exceeded iteration limit {cfg.max_steps}") >>
                                   trace results.reverse >> 
                                   failed   
| ⟨ _,      results, [] ⟩      := (pure results)
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                    (pure results)
                                    (do if cfg.trace_steps then trace format!"trying chain tactic #{tactics.length - ts.length}" else skip,
                                        dependent_if_then_else t 
                                          (λ result, (if cfg.trace_steps then trace format!"succeeded with result: {result}" else skip)
                                                       >> (chain' ⟨ n, result :: results, tactics ⟩ ))
                                          (chain' ⟨ succ n, results, ts ⟩)
                                    )

meta def chain { α : Type } [ has_to_format α ] 
  ( tactics        : list (tactic α) )
  ( cfg     : chain_cfg := {} )
    : tactic (list α) :=
do sequence ← chain' cfg tactics ⟨ cfg.max_steps, [], tactics ⟩,
   guard (sequence.length ≠ 0) <|> fail "...chain tactic made no progress",
   pure sequence.reverse