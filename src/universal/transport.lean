set_option pp.all true

lemma transport_refl { α : Type } ( a b : α ) ( p : a = b ) : @eq.rec α a _ (eq.refl a) b p = eq.refl b :=
begin
  simp
end

lemma transport_refl' { α : Type } ( a b c : α ) ( p : b = c ) : @eq.rec α b _ (eq.refl (a, b)) c p = eq.refl (a, c) :=
begin
  simp
end

lemma transport_Prop ( P Q : Prop ) ( a : P ) ( p : P = Q ) : @eq.rec Prop P (λ T, T) a Q p = eq.mp p a := begin
  reflexivity
end

--(eq.rec (eq.refl (prod.mk fst)) p)

lemma foo { α β : Type } ( a b : α ) ( p : a = b ) : @eq.rec α a _ (eq.refl (@prod.mk α β a)) b p = eq.refl (@prod.mk α β b) := by simp