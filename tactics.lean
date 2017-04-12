-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

open tactic

def pointwise_attribute : user_attribute := {
  name := `pointwise,
  descr := "A lemma that proves things are equal using the fact they are pointwise equal."
}

run_cmd attribute.register `pointwise_attribute

def unfoldable_attribute : user_attribute := {
  name := `unfoldable,
  descr := "A definition that may be unfoldable, but hesitantly."
}

run_cmd attribute.register `unfoldable_attribute

/- Try to apply one of the given lemas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic unit
| []      := failed
| (c::cs) := (mk_const c >>= fapply /->> trace ("applying " ++ to_string c)-/) <|> any_apply cs

section
open smt_tactic
meta def smt_simp   : tactic unit := using_smt $ intros >> try dsimp >> try simp
meta def smt_eblast : tactic unit := using_smt $ intros >> try dsimp >> try simp >> try eblast
meta def smt_ematch : tactic unit := using_smt $ intros >> smt_tactic.add_lemmas_from_facts >> try ematch
end

meta def pointwise_and_then (and_then : tactic unit) : tactic unit :=
do cs ← attribute.get_instances `pointwise,
   seq (any_apply cs) and_then

meta def force_pointwise : tactic unit := pointwise_and_then skip
meta def pointwise : tactic unit := try ( force_pointwise )

attribute [reducible] cast
attribute [reducible] lift_t coe_t coe_b
attribute [simp] id_locked_eq
attribute [pointwise] funext
attribute [ematch] subtype.property

open tactic
open lean.parser
open interactive

-- meta def force { α : Type } (t : tactic α) : tactic α :=
--   do 
--      hypotheses ← local_context,
--      goals ← get_goals,
--      result ← t,
--      hypotheses' ← local_context,
--      goals' ← get_goals,
--      guard ((goals ≠ goals') || (hypotheses ≠ hypotheses')) <|> fail "force tactic failed",
--      return result
meta def force { α : Type } (t : tactic α) : tactic α :=
  do 
     goals ← get_goals,
     result ← t,
     goals' ← get_goals,
     guard (goals ≠ goals') <|> fail "force tactic failed",
     return result

namespace tactic.interactive
  meta def force (t : itactic) : tactic unit := _root_.force t
end tactic.interactive

meta def dunfold_core' (m : transparency) (max_steps : nat) (e : expr) : tactic expr :=
let unfold (u : unit) (e : expr) : tactic (unit × expr × bool) := do
  guard (e.is_app),
  new_e ← dunfold_expr_core m e,
  return (u, new_e, ff)
in do (c, new_e) ← dsimplify_core () max_steps tt ff (λ c e, failed) unfold e,
      return new_e

meta def dunfold_and_simp (m : transparency) (max_steps : nat) (e : expr) : tactic expr :=
do s ← simp_lemmas.mk_default,
let unfold (u : unit) (e : expr) : tactic (unit × expr × bool) := do
  guard (e.is_app),
  new_e ← dunfold_expr_core m e,
  new_e_simp ← s.dsimplify new_e,
  return (u, new_e_simp, tt)
in do (c, new_e) ← dsimplify_core () max_steps tt ff (λ c e, failed) unfold e,
      return new_e

-- This tactic is a combination of dunfold_at and dsimp_at_core
meta def dunfold_and_simp_at (s : simp_lemmas) (h : expr) : tactic unit :=
do num_reverted ← revert h,
   (expr.pi n bi d b : expr) ← target,
   new_d ← dunfold_core' reducible default_max_steps d,
   new_d_simp ← s.dsimplify new_d,
   change $ expr.pi n bi new_d_simp b,
   intron num_reverted

meta def dunfold_and_simp_all_hypotheses : tactic unit :=
do l ← local_context,
   s ← simp_lemmas.mk_default,
   l.reverse.mfor' $ λ h, do
     try (dunfold_and_simp_at s h)

meta def dsimp_all_hypotheses : tactic unit :=
do l ← local_context,
   l.reverse.mfor' $ λ h, do
     try (dsimp_at h)

open lean.parser
open interactive

-- #eval default_max_steps

meta def dunfold_everything : tactic unit := target >>= dunfold_core' reducible /-default_max_steps-/ 1000000 >>= change
meta def dunfold_everything' : tactic unit := dunfold_everything >> try dsimp >> try simp
-- do goals ← get_goals,
--    dunfold_everything,
--    try dsimp,
--    try simp,
--    trace goals,
--    goals' ← get_goals,
--    if goals ≠ goals' then dunfold_everything' else skip

-- dunfold_everything >> try dsimp >> try ( seq simp dunfold_everything' )
-- meta def dunfold_everything' : nat → tactic unit
-- | 0            := trace "dunfold_everything seems to be stuck in a loop" >> failed
-- | (nat.succ n) := dunfold_everything >> try dsimp >> try ( seq simp (dunfold_everything' n) )

meta def unfold_unfoldable : tactic unit := 
  dunfold_and_simp_all_hypotheses >> dunfold_everything'

-- TODO try using get_unused_name
meta def new_names ( e : expr ) : list name :=
  [ 
    name.append (e.local_pp_name) (mk_simple_name "_1"), 
    name.append (e.local_pp_name) (mk_simple_name "_2")
  ]

meta def induction_on_pairs : tactic unit :=
repeat( do l ← local_context,
   l.reverse.mfor' $ λ h, do
     ```(prod _ _) ← infer_type h >>= whnf | skip,
     induction h (new_names h) >> skip )

meta def induction_on_unit : tactic unit :=
do l ← local_context,
   l.reverse.mfor' $ λ h, do
     ```(unit) ← infer_type h >>= whnf | skip,
     induction h >> skip

meta def automatic_inductions : tactic unit :=
  induction_on_pairs >> induction_on_unit

meta def intros_and_inductions : tactic unit := intros >> automatic_inductions >> dsimp_all_hypotheses

meta def fsplit : tactic unit :=
do [c] ← target >>= get_constructors_for | tactic.fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= fapply

-- meta def split_goals' : expr → tactic unit
-- | ```(and _ _)     := split
-- | ```(nonempty _)  := split
-- | ```(unit)        := split
-- | ```(punit)       := split
-- | ```(plift _)     := split
-- | ```(ulift _)     := split
-- -- | ```(subtype _)  := fsplit
-- | _                := failed

-- meta def split_goals : tactic unit := target >>= split_goals'

-- meta def split_goals_and_then ( and_then : tactic unit ) := try ( seq split_goals and_then )

meta def trace_goal_type : tactic unit :=
do g ← target,
   trace g,
   infer_type g >>= trace,
   skip

attribute [pointwise] and.intro
attribute [pointwise] nonempty.intro
attribute [pointwise] unit.star
attribute [pointwise] punit.star
attribute [pointwise] plift.up
attribute [pointwise] ulift.up
attribute [pointwise] prod.mk
attribute [pointwise] pprod.mk
attribute [pointwise] subtype.mk

-- open tactic.interactive
-- meta def blast  : tactic unit := intros >> try ( pointwise_and_then blast ) >> unfold_unfoldable >> try smt_eblast >> try ( pointwise_and_then blast ) -- >> split_goals_and_then blast

meta def done : tactic unit :=
  do goals ← get_goals,
     guard (goals = []),
     trace "no goals",
     skip
open nat

private meta def chain' ( tactics : list (tactic unit) ) : nat → list (tactic unit) → tactic unit
| 0        _         := trace "... 'chain' tactic exceeded iteration limit" >> failed   
| _        []        := done <|> trace "We've tried all tactics in the chain, but there are still unsolved goals." -- We've run out of tactics to apply!
| (succ n) (t :: ts) := done <|> (seq t (chain' n tactics)) <|> chain' (succ n) ts

meta def chain ( tactics : list (tactic unit) ) : tactic unit := chain' tactics 1000 tactics

meta def auto : tactic unit := chain [ force ( intros >> skip ), force_pointwise ]
meta def auto' : tactic unit := chain [ force ( intros >> skip ), force_pointwise, force ( smt_eblast ) ]

meta def blast : tactic unit :=
  -- trace "starting blast" >>
  chain [
    force ( intros >> skip ),
    force_pointwise,
    /-dunfold_and_simp_all_hypotheses >>-/ force ( dunfold_everything' ),
    force ( smt_eblast )
  ]

-- In a timing test on 2017-02-18, I found that using `abstract { blast }` instead of just `blast` resulted in a 5x speed-up!
notation `♮` := by abstract { smt_eblast }
notation `♯` := by abstract { blast }

set_option formatter.hide_full_terms false

@[simp] lemma {u v} pair_1 {α : Type u} {β : Type v} { a: α } { b : β } : (a, b).fst = a := ♮
@[simp] lemma {u v} pair_2 {α : Type u} {β : Type v} { a: α } { b : β } : (a, b).snd = b := ♮
@[simp,ematch] lemma {u v} pair_equality {α : Type u} {β : Type v} { X: α × β }: (X.fst, X.snd) = X :=
begin
  induction X,
  blast,
end
@[pointwise] lemma {u v} pair_equality_3 {α : Type u} {β : Type v} { X: α × β } { A : α } ( p : A = X.fst ) { B : β } ( p : B = X.snd ) : (A, B) = X := begin induction X, blast end
@[pointwise] lemma {u v} pair_equality_4 {α : Type u} {β : Type v} { X Y : α × β } ( p1 : X.1 = Y.1 ) ( p2 : X.2 = Y.2 ) : X = Y := begin induction X, blast end
@[pointwise] lemma {u v} dependent_pair_equality {α : Type u} {Z : α → Type v} { X Y : Σ a : α, Z a } ( p1 : X.1 = Y.1 ) ( p2 : @eq.rec α X.1 Z X.2 Y.1 p1 = Y.2 ) : X = Y := begin induction X, induction Y, blast end
@[pointwise] lemma {u} punit_equality ( X Y : punit.{u} ) : X = Y := begin induction X, induction Y, blast end
@[pointwise] lemma {u} plift_equality { α : Sort u } ( X Y : plift α ) ( p : X.down = Y.down ) : X = Y := begin induction X, induction Y, blast end
@[pointwise] lemma {u v} ulift_equality { α : Type v } ( X Y : ulift.{u v} α ) ( p : X.down = Y.down ) : X = Y := begin induction X, induction Y, blast end
attribute [pointwise] subtype.eq

@[reducible] def {u} auto_cast {α β : Sort u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Sort u} (a : α) : @auto_cast α α (by smt_ematch) a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ (by smt_ematch) p

definition {u v} transport {A : Type u} { P : A → Type v} {x y : A} (p : x = y)
(u : P x) : P y :=
by induction p; exact u

-- TODO this is destined for the standard library?
meta def mk_inhabitant_using (A : expr) (t : tactic unit) : tactic expr :=
do m ← mk_meta_var A,
   gs ← get_goals,
   set_goals [m],
   t,
   r ← instantiate_mvars m,
   set_goals gs,
   return r

namespace tactic
meta def apply_and_mk_decl (n : name) (tac : tactic unit) : tactic unit := do
 t ← target,
 val ← mk_inhabitant_using t  tac,
 add_aux_decl n t val tt,
 apply val

meta def tag_as_simp (n: name) : tactic unit := set_basic_attribute `simp n 
-- TODO this doesn't work:
meta def tag_as_ematch (n: name) : tactic unit := set_basic_attribute `ematch n 

namespace interactive
open lean.parser
open interactive

meta def apply_and_mk_decl (n : parse ident) (tac : itactic) : tactic unit :=
tactic.apply_and_mk_decl n tac

-- TODO restore tag_as_ematch when it works
meta def apply_and_mk_simp_decl (n : parse ident) (tac : itactic) : tactic unit :=
tactic.apply_and_mk_decl n tac >> tag_as_simp n -- >> tag_as_ematch n

meta def apply_and_mk_ematch_decl (n : parse ident) (tac : itactic) : tactic unit :=
tactic.apply_and_mk_decl n tac >> tag_as_ematch n

meta def blast_as_simp (n : parse ident) : tactic unit := tactic.interactive.apply_and_mk_simp_decl n blast
meta def blast_as_ematch (n : parse ident) : tactic unit := tactic.interactive.apply_and_mk_ematch_decl n blast
meta def blast_as (n : parse ident) : tactic unit := tactic.interactive.apply_and_mk_decl n blast

meta def blast_simp : tactic unit := mk_fresh_name >>= blast_as_simp
meta def blast_ematch : tactic unit := mk_fresh_name >>= blast_as_ematch

end interactive
end tactic
