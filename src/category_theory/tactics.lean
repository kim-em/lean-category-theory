-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

-- FIXME this should not be here, but I don't know how to make 'automatic_inductions', below, updateable. Use attributes?
inductive Two : Type
| _0 : Two
| _1 : Two

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

-- Applies a list of tactics in turn, always succeeding.
meta def list_try_seq : list (tactic unit) → tactic unit 
| list.nil  := skip
| (t :: ts) := seq (try t) (list_try_seq ts)

-- Applies a list of tactics in turn, succeeding if at least one succeeds.
meta def at_least_one : list (tactic unit) → tactic unit
| list.nil  := fail "at_least_one tactic failed, no more tactics"
| (t :: ts) := (seq t (list_try_seq ts)) <|> (at_least_one ts)

private meta def unfold_projections_core' (m : transparency) (max_steps : nat) (e : expr) : tactic expr :=
let unfold (changed : bool) (e : expr) : tactic (bool × expr × bool) := do
  new_e ← unfold_projection_core m e,
  return (tt, new_e, tt)
in do (tt, new_e) ← dsimplify_core ff default_max_steps tt (λ c e, failed) unfold e | fail "no projections to unfold",
      return new_e

-- meta def unfold_projections' : tactic unit :=
-- target >>= unfold_projections_core' semireducible default_max_steps >>= change

meta def unfold_projections_at' (h : expr) : tactic unit :=
do num_reverted ← revert h,
   (expr.pi n bi d b : expr) ← target,
   new_d ← unfold_projections_core' semireducible default_max_steps d,
   change $ expr.pi n bi new_d b,
   intron num_reverted

meta def unfold_projections_hypotheses : tactic unit :=
do l ← local_context,
   s ← simp_lemmas.mk_default,
   at_least_one (l.reverse.for (λ h, unfold_projections_at' h)) <|> fail "fail no projections to unfold in hypotheses"   

meta def unfold_projections_hypotheses' : tactic unit := `[unfold_projections at *] -- BUG see the problem in discrete_category.lean

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

-- We make a local version of simp_at, which only succeeds if it changes something, *and* successfully clears the old hypothesis.
meta def simp_at' (h : expr) (extra_lemmas : list expr := []) (cfg : simp_config := {}) : tactic unit :=
do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   S     ← simp_lemmas.mk_default,
   S     ← S.append extra_lemmas,
   (new_htype, heq) ← simplify S htype cfg,
   guard (new_htype ≠ htype) <|> fail "simp_at didn't do anything",
   assert (expr.local_pp_name h) new_htype,
   mk_eq_mp heq h >>= exact,
   clear h <|> fail "simp_at' could not clear the original hypothesis"

meta def simp_hypotheses : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, simp_at' h)) <|> fail "simp_hypothesis did not simplify anything"

meta def simp_hypotheses' : tactic unit := `[simp at *] -- FIXME useless at the moment, since this always succeeds

meta def new_names ( e : expr ) : tactic (list name) :=
  do 
    n1 ← get_unused_name e.local_pp_name (some 1), 
    n2 ← get_unused_name e.local_pp_name (some 2),
    pure [ n1, n2 ] 

meta def automatic_induction_at (h : expr) : tactic unit :=
do t ← infer_type h,
match t with
| `(unit)      := induction h >>= λ x, skip
| `(punit)     := induction h >>= λ x, skip
| `(false)     := induction h >>= λ x, skip
| `(empty)     := induction h >>= λ x, skip
| `(fin nat.zero) := induction h >>= λ x, `[cases is_lt]
| `(Two)       := induction h >>= λ x, skip
| `(ulift _)   := induction h >>= λ x, skip
| `(plift _)   := induction h >>= λ x, skip
| `(eq _ _)    := induction h >>= λ x, skip
| `(prod _ _)  := do names ← new_names h,
                      induction h >> skip
| `(sigma _)   := do names ← new_names h,
                      induction h >> skip
| `(subtype _) := do names ← new_names h,
                      induction h names >> skip
| _              := failed
end

meta def automatic_induction : tactic unit :=
do l ← local_context,
   at_least_one (l.reverse.for (λ h, automatic_induction_at h))

open lean.parser
open interactive

meta def fsplit : tactic unit :=
do [c] ← target >>= get_constructors_for | tactic.fail "fsplit tactic failed, target is not an inductive datatype with only one constructor",
   mk_const c >>= fapply

namespace tactic

meta def repeat_at_least_once ( t : tactic unit ) : tactic unit := t >> repeat t

namespace interactive
meta def repeat_at_least_once : itactic → tactic unit :=
tactic.repeat_at_least_once
end interactive

end tactic


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
     | `(%%lhs = %%rhs) := pure (lhs, rhs)
     | `(%%lhs == %%rhs) := pure (lhs, rhs)
     | _ := fail "goal is not an equality"
     end,
     pre ← common_app_prefix lhs rhs,
     l ← mk_hcongr_lemma pre,
     tactic.apply l.proof,
     all_goals $ try refl

  /-- Given a goal that equates two structure values, this tactic breaks it down to subgoals equating each
      pair of fields. -/
  meta def congr_struct : tactic unit :=
  do `(%%lhs = %%rhs) ← target | fail "goal is not an equality",
     ty ← infer_type lhs,
     eta ← mk_struct_eta ty,
     apply ``(@eq.rec _ _ (λ lhs, lhs = %%rhs) _ _ %%(app eta lhs)),
     `(%%new_lhs = %%rhs) ← target,
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

open nat

-- PROJECT make this less lame
meta def nat_inequality : tactic unit :=
do tgt ← target,
match tgt with
| `(%%lhs < %%rhs) := `[apply nat.lt_succ_of_le]     -- TODO how to check lhs and rhs are actually nat's?
| `(%%lhs ≤ %%rhs) := `[rewrite nat.le_iff_lt_or_eq, simp]
| _                := failed
end

-- lemma f : 0 < 2 :=
-- begin
--  nat_inequality,
--  nat_inequality,
--  nat_inequality,
--  nat_inequality,
-- end


private meta def if_then_else { α : Type } ( i : tactic unit ) ( t e : tactic α ) : tactic α :=
do r ← (i >> pure tt) <|> pure ff,
   if r then do t else do e
private meta def dependent_if_then_else { α β : Type } ( i : tactic α ) ( t : α → tactic β ) ( e : tactic β ) : tactic β :=
do r ← tactic.try_core i,
   match r with
   | some a := t a
   | none   := e
   end

private meta structure chain_progress :=
  ( iteration_limit   : nat )
  ( results           : list string )
  ( remaining_tactics : list (tactic string) )

private meta def chain' ( tactics : list (tactic string) ) : chain_progress → tactic (list string)
| ⟨ 0,      results, _ ⟩       := trace "... chain tactic exceeded iteration limit" >>
                                   trace results.reverse.to_string >> 
                                   failed   
| ⟨ _,      results, [] ⟩      := (pure results)
| ⟨ succ n, results, t :: ts ⟩ := if_then_else done
                                    (pure results)
                                    (dependent_if_then_else t 
                                      (λ result, (chain' ⟨ n, result :: results, tactics ⟩ ))
                                      (chain' ⟨ succ n, results, ts ⟩)
                                    )

private def chain_default_max_steps := 500

meta def chain
  ( tactics        : list (tactic string) )
  ( max_steps      : nat  := chain_default_max_steps )
    : tactic (list string) :=
do sequence ← chain' tactics ⟨ max_steps, [], tactics ⟩,
   guard (sequence.length ≠ 0) <|> fail "...chain tactic made no progress",
   pure sequence.reverse

-- meta def unfold_unfoldable ( max_steps : nat := chain_default_max_steps ) : tactic unit := 
--    chain [
--       force ( dsimp ),
--       simp,
--       unfold_projections,

--       dsimp_hypotheses,
--       simp_hypotheses,
--       unfold_projections_hypotheses,

--       dunfold_everything
--   ] max_steps

private meta def dsimp_eq_mpr : tactic unit := `[dsimp [eq.mpr]]


section
open smt_tactic
meta def smt_simp   : tactic unit := using_smt $ intros >> try dsimp >> try simp
meta def smt_eblast : tactic unit := using_smt $ intros >> try dsimp >> unfold_coe >> try simp >> eblast
meta def smt_ematch : tactic unit := using_smt $ intros >> smt_tactic.add_lemmas_from_facts >> try ematch
end

meta def tidy_tactics : list (tactic string) :=
[
  ( tactic.triv,                   "triv" ),
  ( force (reflexivity),           "refl" ),
  ( nat_inequality,                "nat_inequality" ),
  ( pointwise,                     "pointwise" ),
  ( force (intros >> skip),        "intros" ),
  ( force (fsplit),                "fsplit" ),
  ( force (dsimp_eq_mpr),          "dsimp [eq.mpr]" ),
  ( unfold_projections,            "unfold_projections" ),
  ( simp,                          "simp" ),
  ( dsimp_hypotheses,              "dsimp_hypotheses" ),
  ( automatic_induction,           "automatic_induction" ),
  ( unfold_projections_hypotheses, "unfold_projections_hypotheses" ),
  ( simp_hypotheses,               "simp_hypotheses" )
].map $ λ p, p.1 >> (pure p.2)

meta def tidy ( max_steps : nat := chain_default_max_steps ) ( trace_progress : bool := ff ) : tactic unit :=
do results ← chain tidy_tactics max_steps,
   if trace_progress then
     trace ("... chain tactic used: " ++ results.to_string)
   else
     skip

meta def blast ( max_steps : nat := chain_default_max_steps ) ( trace_progress : bool := ff ) : tactic unit := 
do results ← chain (tidy_tactics ++ [ any_goals ( smt_eblast >> done ) >> pure "smt_eblast" ]) max_steps,
   if trace_progress then
     trace ("... chain tactic used: " ++ results.to_string)
   else
     skip

notation `♮` := by abstract { smt_eblast }
notation `♯` := by abstract { blast }

set_option formatter.hide_full_terms false

@[simp] lemma {u v} pair_1 {α : Type u} {β : Type v} { a : α } { b : β } : (a, b).1 = a := ♮
@[simp] lemma {u v} pair_2 {α : Type u} {β : Type v} { a : α } { b : β } : (a, b).2 = b := ♮
@[simp,ematch] lemma {u v} pair_equality {α : Type u} {β : Type v} { X : α × β } : (X.1, X.2) = X := ♯
@[pointwise] lemma {u v} pairs_componentwise_equal {α : Type u} {β : Type v} { X Y : α × β } ( p1 : X.1 = Y.1 ) ( p2 : X.2 = Y.2 ) : X = Y := ♯
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