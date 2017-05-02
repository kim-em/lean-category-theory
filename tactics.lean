-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

open tactic

def pointwise_attribute : user_attribute := {
  name := `pointwise,
  descr := "A lemma that proves things are equal using the fact they are pointwise equal."
}

run_cmd attribute.register `pointwise_attribute

/- Try to apply one of the given lemas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic unit
| []      := failed
| (c::cs) := (mk_const c >>= fapply /->> trace ("applying " ++ to_string c)-/) <|> any_apply cs

meta def pointwise : tactic unit :=
do cs ← attribute.get_instances `pointwise,
   any_apply cs

attribute [reducible] cast
attribute [reducible] lift_t coe_t coe_b has_coe_to_fun.coe
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

-- meta def dunfold_core (m : transparency) (max_steps : nat) (cs : list name) (e : expr) : tactic expr :=
-- let unfold (u : unit) (e : expr) : tactic (unit × expr × bool) := do
--   guard (cs.any e.is_app_of),
--   new_e ← dunfold_expr_core m e,
--   return (u, new_e, tt)
-- in do (c, new_e) ← dsimplify_core () max_steps tt (λ c e, failed) unfold e,
--       return new_e

meta def dunfold_core' (m : transparency) (max_steps : nat) (e : expr) : tactic expr :=
let unfold (changed : bool) (e : expr) : tactic (bool × expr × bool) := do
  new_e ← dunfold_expr_core m e,
  return (tt, new_e, ff)
in do (tt, new_e) ← dsimplify_core ff max_steps tt (λ c e, failed) unfold e | fail "nothing to unfold",
      return new_e

-- This tactic is a combination of dunfold_at and dsimp_at_core
meta def dunfold_and_simp_at (s : simp_lemmas) (h : expr) : tactic unit :=
do num_reverted ← revert h,
   (expr.pi n bi d b : expr) ← target,
   new_d ← dunfold_core' semireducible default_max_steps d,
   new_d_simp ← s.dsimplify new_d,
   guard (new_d_simp ≠ d),
   change $ expr.pi n bi new_d_simp b,
   intron num_reverted

-- Applies a list of tactics in turn, always succeeding.
meta def list_try_seq : list (tactic unit) → tactic unit 
| list.nil  := skip
| (t :: ts) := seq (try t) (list_try_seq ts)

-- Applies a list of tactics in turn, succeeding if at least one succeeds.
meta def at_least_one : list (tactic unit) → tactic unit
| list.nil  := fail "at_least_one tactic failed, no more tactics"
| (t :: ts) := (seq t (list_try_seq ts)) <|> (at_least_one ts)

meta def unfold_projections_hypotheses : tactic unit :=
do l ← local_context,
   s ← simp_lemmas.mk_default,
   at_least_one (l.reverse.for (λ h, unfold_projections_at h)) <|> fail "fail no projections to unfold in hypotheses"

-- meta def unfold_hypotheses : tactic unit :=
-- do l ← local_context,
--    s ← simp_lemmas.mk_default,
--    at_least_one (l.reverse.for (λ h, dunfold_and_simp_at s h))

-- We need our own version of dsimp_at_core, which fails when it can't do anything.
meta def dsimp_at_core' (s : simp_lemmas) (h : expr) : tactic unit :=
do num_reverted : ℕ ← revert h,
   expr.pi n bi d b ← target,
   h_simp ← s.dsimplify d,
   guard (h_simp ≠ d) <|> fail "dsimp tactic did not simplify",
   change $ expr.pi n bi h_simp b,
   intron num_reverted

meta def dsimp_at' (h : expr) : tactic unit :=
do s ← simp_lemmas.mk_default, dsimp_at_core' s h

meta def dsimp_hypotheses : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, dsimp_at' h)) <|> fail "dsimp could not simplify any hypothesis"

-- FIXME let's try this
-- meta def simp_at_via_rewrite (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
-- do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
--    htype ← infer_type h,
--    S     ← simp_lemmas.mk_default,
--    S     ← S.append extra_lemmas,
--    (new_htype, heq) ← simplify S htype cfg,
--    rewrite_at_core reducible tt tt occurrences.all ff heq h

-- @[pointwise] lemma {u v} dependent_pair_equality' {α : Type u} {Z : α → Type v} { X Y : Σ a : α, Z a } ( p1 : X.1 = Y.1 ) ( p2 : @eq.rec α X.1 Z X.2 Y.1 p1 = Y.2 ) : X = Y := begin induction X, induction Y, simp at p1, end

-- We make a local version of simp_at, which only succeeds if it changes something, and successfully clears the old hypothesis.
meta def simp_at' (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk_default,
   S     ← S.append extra_lemmas,
   (new_htype, heq) ← simplify S htype cfg,
   guard (new_htype \ne )
   assert (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   clear h


meta def simp_hypotheses : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, simp_at h))

meta def new_names ( e : expr ) : tactic (list name) :=
  do 
    n1 ← get_unused_name e.local_pp_name (some 1), 
    n2 ← get_unused_name e.local_pp_name (some 2),
    pure [ n1, n2 ] 

-- meta def induction_on_pairs : tactic unit :=
--  do l ← local_context,
--    at_least_one (
--    l.reverse.for (λ h, do
--      t ← infer_type h >>= whnf,
--      match t with
--      | ```(prod _ _) := do names ← new_names h,
--                            induction h names >> skip
--      | _             := fail "hypothesis is not a pair"
--      end)) <|> fail "no hypotheses are pairs"

meta def automatic_induction' (h : expr) (t : expr) : tactic unit :=
match t with
| ```(unit)      := induction h >>= λ x, skip
| ```(punit)     := induction h >>= λ x, skip
| ```(empty)     := induction h >>= λ x, skip
| ```(ulift _)   := induction h >>= λ x, skip
| ```(plift _)   := induction h >>= λ x, skip
| ```(prod _ _)  := do names ← new_names h,
                      induction h names >> skip
| ```(sigma _)   := do names ← new_names h,
                      induction h names >> skip
| _              := failed
end

meta def automatic_induction_at (h : expr) : tactic unit :=
do t ← infer_type h,
   automatic_induction' h t

meta def automatic_induction : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, automatic_induction_at h))

open lean.parser
open interactive

meta def dunfold_everything : tactic unit := target >>= dunfold_core' reducible default_max_steps >>= change

meta def fsplit : tactic unit :=
do [c] ← target >>= get_constructors_for | tactic.fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= fapply

namespace tactic
  open expr

  /-- Given a fully applied structure type `ty` with fields `f1`...`fn`, synthesize the proof
      `∀ x : ty, ty.mk x.f1 ... x.fn = x`.
      The proof can be extracted into a new definition using

      ```
      def ty.eta := by mk_struct_eta ```(ty) >>= exact
      ``` -/
  meta def mk_struct_eta (ty : expr) : tactic expr :=
  do (const n ls) ← pure ty.get_app_fn | fail "not a structure",
     env ← get_env,
     fields ← env.structure_fields n <|> fail "not a structure",
     [ctor] ← pure $ env.constructors_of n,
     let ctor := (const ctor ls).mk_app ty.get_app_args,
     x ← mk_local_def `x ty,
     fields ← fields.mmap $ λ f, to_expr (pexpr.mk_field_macro (pexpr.of_expr x) f),
     proof_ty ← mk_app ``eq [ctor.mk_app fields, x],
     prod.snd <$> solve_aux (pis [x] proof_ty) (do x ← intro `_, cases x, reflexivity)
end tactic

namespace tactic.interactive
  open expr tactic

  private meta def common_app_prefix : expr → expr → tactic expr
  | (app e₁ e₁') (app e₂ e₂') := (is_def_eq e₁ e₂ *> pure e₁) <|> common_app_prefix e₁ e₂
  | e₁           e₂           := fail "no common head symbol"

  /-- Given a goal of form `f a₁ ... aₙ == f a₁' ... aₙ'`, this tactic breaks it down to subgoals
      `a₁ == a₁'`, ...
      Subgoals provable by reflexivity are dispensed automatically.
      The goal can also be a homogenous equality. New subgoals will use homogenous equalities where possible. -/
  meta def congr_args : tactic unit :=
  do tgt ← target,
     (lhs, rhs) ← match tgt with
     | ```(%%lhs = %%rhs) := pure (lhs, rhs)
     | ```(%%lhs == %%rhs) := pure (lhs, rhs)
     | _ := fail "goal is not an equality"
     end,
     pre ← common_app_prefix lhs rhs,
     l ← mk_hcongr_lemma pre,
     tactic.apply l.proof,
     all_goals $ try refl

  /-- Given a goal that equates two structure values, this tactic breaks it down to subgoals equating each
      pair of fields. -/
  meta def congr_struct : tactic unit :=
  do ```(%%lhs = %%rhs) ← target | fail "goal is not an equality",
     ty ← infer_type lhs,
     eta ← mk_struct_eta ty,
     apply ``(@eq.rec _ _ (λ lhs, lhs = %%rhs) _ _ %%(app eta lhs)),
     ```(%%new_lhs = %%rhs) ← target,
     apply ``(@eq.rec _ _ (λ rhs, %%new_lhs = rhs) _ _ %%(app eta rhs)),
     congr_args
end tactic.interactive

-- congr_struct needs various helper lemmas.
@[pointwise] lemma heq_prop { α β : Prop } { a : α } { b : β } ( h : α = β ) : a == b :=
begin
  induction h, reflexivity
end

@[pointwise] theorem {u v w z} funext_prop_001 { α : Type u } { β : Type v } { Z : α → β → Type w } { X : Π ( a : α ) ( b : β ) ( g : Z a b ), Type z }
                          { p q r s : Π ( a : α ) ( b : β ) ( g : Z a b ), X a b g }
                          ( h1 : p = r ) ( h2 : q = s )
                       : (∀ ( a : α ) ( b : β ) ( g : Z a b ), p a b g = q a b g ) = (∀ ( a : α ) ( b : β ) ( g : Z a b), r a b g = s a b g ) :=
begin
  induction h1,
  induction h2,
  reflexivity
end

meta def trace_goal_type : tactic unit :=
do g ← target,
   trace g,
   infer_type g >>= trace,
   skip

meta def unfold_coe : tactic unit := tactic.dunfold [ ``has_coe_to_fun.coe ]

section
open smt_tactic
meta def smt_simp   : tactic unit := using_smt $ intros >> try dsimp >> try simp
meta def smt_eblast : tactic unit := using_smt $ intros >> try dsimp >> unfold_coe >> try simp >> try eblast
meta def smt_ematch : tactic unit := using_smt $ intros >> smt_tactic.add_lemmas_from_facts >> try ematch
end


attribute [pointwise] and.intro
attribute [pointwise] nonempty.intro
attribute [pointwise] unit.star
attribute [pointwise] punit.star
attribute [pointwise] plift.up
attribute [pointwise] ulift.up
attribute [pointwise] prod.mk
attribute [pointwise] pprod.mk
attribute [pointwise] subtype.mk

meta def done : tactic unit :=
  do goals ← get_goals,
     guard (goals = []),
    --  trace "no goals",
     skip

-- meta def monitor_progress { α : Type } ( t : tactic α ) : tactic (bool × α) :=
-- do goals ← get_goals,
--    result ← t,
--    goals' ← get_goals,
--    return (goals ≠ goals', result)

open nat

private meta def chain' ( tactics : list (tactic unit) ) : nat → list (tactic unit) → tactic unit
| 0        _         := trace "... 'chain' tactic exceeded iteration limit" >> failed   
| _        []        := done <|> /-trace "We've tried all tactics in the chain, but there are still unsolved goals." >>-/ skip -- We've run out of tactics to apply!
| (succ n) (t :: ts) := done <|> /-trace (list.length ts) >>-/ (seq (all_goals t) (chain' n tactics)) <|> chain' (succ n) ts

meta def chain ( tactics : list (tactic unit) ) : tactic unit := chain' tactics 50 tactics

meta def unfold_unfoldable : tactic unit := 
   chain [
      dsimp_hypotheses,
      force ( dsimp ),
      simp,
      unfold_projections_hypotheses,
      unfold_projections,
      dunfold_everything
  ]

meta def tidy : tactic unit := 
   chain [
      tactic.triv,
      force ( reflexivity ),
      assumption,
      dsimp_hypotheses,
      force ( dsimp ),
      -- simp_hypotheses,
      simp,
      unfold_projections_hypotheses,
      unfold_projections,
      force ( intros >> skip ),
      automatic_induction,
      pointwise
      -- tactic.interactive.congr_struct
  ]


meta def blast : tactic unit := tidy >> all_goals (try smt_eblast)

notation `♮` := by abstract { smt_eblast }
notation `♯` := by abstract { blast }

set_option formatter.hide_full_terms false

@[simp] lemma {u v} pair_1 {α : Type u} {β : Type v} { a: α } { b : β } : (a, b).fst = a := ♮
@[simp] lemma {u v} pair_2 {α : Type u} {β : Type v} { a: α } { b : β } : (a, b).snd = b := ♮
@[simp,ematch] lemma {u v} pair_equality {α : Type u} {β : Type v} { X: α × β }: (X.fst, X.snd) = X := ♯
@[pointwise] lemma {u v} pair_equality_3 {α : Type u} {β : Type v} { X: α × β } { A : α } ( p : A = X.fst ) { B : β } ( p : B = X.snd ) : (A, B) = X := ♯
@[pointwise] lemma {u v} pair_equality_4 {α : Type u} {β : Type v} { X Y : α × β } ( p1 : X.1 = Y.1 ) ( p2 : X.2 = Y.2 ) : X = Y := ♯
@[pointwise] lemma {u v} dependent_pair_equality {α : Type u} {Z : α → Type v} { X Y : Σ a : α, Z a } ( p1 : X.1 = Y.1 ) ( p2 : @eq.rec α X.1 Z X.2 Y.1 p1 = Y.2 ) : X = Y := ♯
@[pointwise] lemma {u} punit_equality ( X Y : punit.{u} ) : X = Y := ♯
@[pointwise] lemma {u} plift_equality { α : Sort u } ( X Y : plift α ) ( p : X.down = Y.down ) : X = Y := ♯
@[pointwise] lemma {u v} ulift_equality { α : Type v } ( X Y : ulift.{u v} α ) ( p : X.down = Y.down ) : X = Y := ♯
attribute [pointwise] subtype.eq

@[reducible] def {u} auto_cast {α β : Sort u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Sort u} (a : α) : @auto_cast α α (by smt_ematch) a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ (by smt_ematch) p

definition {u v} transport {A : Type u} { P : A → Type v} {x y : A} (u : P x) (p : x = y) : P y :=
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
