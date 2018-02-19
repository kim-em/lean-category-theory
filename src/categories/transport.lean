@[simp] lemma {u v} congr_refl {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} (h₁ : f₁ = f₂) (a : α) : congr h₁ (eq.refl a) = congr_fun h₁ a :=
begin
  reflexivity,
end

@[simp] lemma {u v} symm_congr_fun {α : Sort u} {β : α → Sort v} {f g : Π x, β x} (h : f = g) (a : α) : eq.symm (congr_fun h a) = congr_fun (eq.symm h) a :=
begin
  reflexivity,
end

@[simp] lemma {u₁ u₂} parallel_transport_for_trivial_bundles {α : Sort u₁} {a b : α} {β : Sort u₂} (p : a = b) (x : β) : @eq.rec α a (λ a, β) x b p = x :=
begin
induction p,
simp,
end
