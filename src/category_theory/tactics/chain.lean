-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .if_then_else

open tactic
open nat

structure chain_cfg := 
  ( max_steps   : nat  := 500 )
  ( trace_steps : bool := ff )

meta def hash_target : tactic string :=
(done >> pure "no goals") <|>
do options ← get_options,
   set_options (options.set_bool `pp.all true),
   t ← read, 
   set_options options,
   pure t.to_format.to_string

private meta structure chain_progress { α : Type } :=
  ( iteration_limit   : nat )
  ( results           : list α )
  ( remaining_tactics : list (tactic α) )
  ( hashes            : list string )

meta def guard_progress { α : Type } ( hashes : list string ) ( t : tactic α ) : tactic ((list string) × α) :=
do r ← t,
   h ← hash_target,
   guard ¬ hashes.mem h <|> trace "chain tactic detected looping" >> failed,
   pure ((h :: hashes), r)

private meta def chain' { α : Type } [ has_to_format α ] ( cfg : chain_cfg ) ( tactics : list (tactic α) ) : chain_progress → tactic (list α)
| ⟨ 0,      results, _, hashes ⟩ := trace (format!"... chain tactic exceeded iteration limit {cfg.max_steps}") >>
                                     trace results.reverse >> 
                                     trace hashes.reverse >>
                                     failed   
| ⟨ _,      results, [], _ ⟩     := (pure results)
| ⟨ succ n, results, t :: ts, hashes ⟩ :=
    if_then_else done
      (pure results)
      (do if cfg.trace_steps then trace format!"trying chain tactic #{tactics.length - ts.length}" else skip,
          dependent_if_then_else (guard_progress hashes t)
            (λ result, do (if cfg.trace_steps then trace format!"succeeded with result: {result.2}" else skip),  
                          (chain' ⟨ n, result.2 :: results, tactics, result.1 ⟩ ))
            (chain' ⟨ succ n, results, ts, hashes ⟩)
      )

meta def chain { α : Type } [ has_to_format α ] 
  ( tactics        : list (tactic α) )
  ( cfg     : chain_cfg := {} )
    : tactic (list α) :=
do sequence ← chain' cfg tactics ⟨ cfg.max_steps, [], tactics, [] ⟩,
   guard (sequence.length ≠ 0) <|> fail "...chain tactic made no progress",
   pure sequence.reverse