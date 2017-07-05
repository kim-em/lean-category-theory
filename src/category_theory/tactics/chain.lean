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

private meta def chain' { α : Type } [ has_to_tactic_format α ] ( tactics : list (tactic α) ) : chain_progress → tactic (list α)
| ⟨ 0,      results, _ ⟩       := trace "... chain tactic exceeded iteration limit" >>
                                   trace results.reverse >> 
                                   failed   
| ⟨ _,      results, [] ⟩      := (pure results)
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                    (pure results)
                                    (dependent_if_then_else t 
                                      (λ result, (chain' ⟨ n, result :: results, tactics ⟩ ))
                                      (chain' ⟨ succ n, results, ts ⟩)
                                    )

def chain_default_max_steps := 500

meta def chain { α : Type } [ has_to_tactic_format α ] 
  ( tactics        : list (tactic α) )
  ( max_steps      : nat  := chain_default_max_steps )
    : tactic (list α) :=
do sequence ← chain' tactics ⟨ max_steps, [], tactics ⟩,
   guard (sequence.length ≠ 0) <|> fail "...chain tactic made no progress",
   pure sequence.reverse