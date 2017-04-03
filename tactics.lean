-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

open tactic
open smt_tactic

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

meta def smt_simp   : tactic unit := using_smt $ intros >> try dsimp >> try simp
meta def smt_eblast : tactic unit := using_smt $ intros >> try dsimp >> try simp >> try eblast
meta def smt_ematch : tactic unit := using_smt $ intros >> add_lemmas_from_facts >> try ematch

meta def pointwise (and_then : tactic unit) : tactic unit :=
do cs ← attribute.get_instances `pointwise,
   try (seq (any_apply cs) and_then)

-- open tactic
attribute [reducible] cast
attribute [reducible] lift_t coe_t coe_b

meta def dunfold_all_at (names : list name) : list expr → tactic unit
| []      := skip
| (H::Hs) := dunfold_at names H >> dsimp_at H >> dunfold_all_at Hs

meta def dunfold_all_hypotheses (names : list name) : tactic unit :=
do hyps ← local_context,
   dunfold_all_at names hyps

open lean.parser
open interactive

meta def dunfold_all (names : list name) : tactic unit :=
dunfold names >> dsimp

meta def unfold_unfoldable_hypotheses : tactic unit := 
do cs ← attribute.get_instances `unfoldable,
   try (dunfold_all_hypotheses cs)

meta def unfold_unfoldable_goals : tactic unit := 
do cs ← attribute.get_instances `unfoldable,
   try (dunfold_all cs)

meta def unfold_unfoldable : tactic unit := 
  unfold_unfoldable_hypotheses >> unfold_unfoldable_goals

-- open tactic.interactive
meta def blast  : tactic unit := intros >> pointwise blast >> try unfold_unfoldable >> try simp >> try smt_eblast >> pointwise blast

-- In a timing test on 2017-02-18, I found that using `abstract { blast }` instead of just `blast` resulted in a 5x speed-up!
notation `♮` := by abstract { smt_eblast }
notation `♯` := by abstract { blast }

@[simp] lemma {u v} pair_1 {α : Type u} {β : Type v} { a: α } { b : β } : (a, b).fst = a := ♮
@[simp] lemma {u v} pair_2 {α : Type u} {β : Type v} { a: α } { b : β } : (a, b).snd = b := ♮
@[simp,ematch] lemma {u v} pair_equality {α : Type u} {β : Type v} { X: α × β }: (X.fst, X.snd) = X := begin induction X, blast end
-- @[pointwise] lemma {u v} pair_equality_1 {α : Type u} {β : Type v} { X: α × β } { A : α } ( p : A = X.fst ) : (A, X.snd) = X := begin induction X, blast end
-- @[pointwise] lemma {u v} pair_equality_2 {α : Type u} {β : Type v} { X: α × β } { B : β } ( p : B = X.snd ) : (X.fst, B) = X := begin induction X, blast end
@[pointwise] lemma {u v} pair_equality_3 {α : Type u} {β : Type v} { X: α × β } { A : α } ( p : A = X.fst ) { B : β } ( p : B = X.snd ) : (A, B) = X := begin induction X, blast end
@[pointwise] lemma {u} punit_equality ( X Y : punit.{u} ) : X = Y := begin induction X, induction Y, blast end
attribute [pointwise] subtype.eq

@[reducible] def {u} auto_cast {α β : Sort u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Sort u} (a : α) : @auto_cast α α (by smt_ematch) a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ (by smt_ematch) p

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

open tactic.interactive
