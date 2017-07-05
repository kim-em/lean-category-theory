-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .applicable

open tactic

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
@[applicable] lemma heq_prop { α β : Prop } { a : α } { b : β } ( h : α = β ) : a == b :=
begin
  induction h, reflexivity
end

@[applicable] theorem {u v w z} funext_prop_001 { α : Type u } { β : Type v } { Z : α → β → Type w } { X : Π ( a : α ) ( b : β ) ( g : Z a b ), Type z }
                          { p q r s : Π ( a : α ) ( b : β ) ( g : Z a b ), X a b g }
                          ( h1 : p = r ) ( h2 : q = s )
                       : (∀ ( a : α ) ( b : β ) ( g : Z a b ), p a b g = q a b g ) = (∀ ( a : α ) ( b : β ) ( g : Z a b), r a b g = s a b g ) :=
begin
  induction h1,
  induction h2,
  reflexivity
end