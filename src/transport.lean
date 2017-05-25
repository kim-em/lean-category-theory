import .tactics

lemma {u v} congr_refl {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} (h₁ : f₁ = f₂) (a : α) : congr h₁ (eq.refl a) = congr_fun h₁ a :=
begin
  reflexivity,
end

lemma {u v} symm_congr_fun {α : Sort u} {β : α → Sort v} {f g : Π x, β x} (h : f = g) (a : α) : eq.symm (congr_fun h a) = congr_fun (eq.symm h) a :=
begin
  reflexivity,
end

-- lemma hfunext {α₁ : Type} {β₁ : Type} {α₂ : Type} {β₂ : Type} { f₁ : α₁ → β₁ } { f₂ : α₂ → β₂ } (hα : α₁ = α₂) : f₁ == f₂ :=
-- begin
-- end

-- meta def its (e : expr) : tactic unit := 
-- do e' ← tactic.unfold_projection e <|> pure e,
--    s ← simp_lemmas.mk_default,
--    e'' ← s.dsimplify e' <|> pure e',
--    tactic.fapply (expr.mk_app (expr.const `transport []) [ e'' ])

-- namespace tactic.interactive
-- open tactic
-- open interactive
-- open interactive.types
-- open lean.parser
-- meta def its (q : parse texpr) : tactic unit :=
-- do tgt : expr ← target,
--    i_to_expr_strict ``(%%q) >>= _root_.its
-- end tactic.interactive

-- def f ( x: nat ) : list nat :=
-- begin
--   its x
-- end