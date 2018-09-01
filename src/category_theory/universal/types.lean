import category_theory.universal.limits
import category_theory.universal.colimits
import category_theory.universal.limits.limits

universe u

open category_theory category_theory.universal

namespace category_theory.universal.types

local attribute [forward] fork.w square.w

instance : has_binary_products.{u+1 u} (Type u) := 
{ prod := λ Y Z, { X := Y × Z, π₁ := prod.fst, π₂ := prod.snd } }

-- FIXME why is this failing?
instance : has_products.{u+1 u} (Type u) := 
{ prod := λ β f, { X := Π b, f b, π := λ b x, x b }, is_product := sorry }.

@[simp] lemma types_pi {β : Type u} (f : β → Type u) : pi f = Π b, f b := rfl
@[simp] lemma types_pi_π {β : Type u} (f : β → Type u) (b : β) : pi.π f b = λ (g : Π b, f b), g b := rfl
@[simp] lemma types_pi_of_components {β : Type u} (f : β → Type u) {P : Type u} (p : Π b, P ⟶ f b) : 
  pi.of_components p = λ q b, p b q :=
begin
  dsimp [pi.of_components],
  sorry
end

instance : has_equalizers.{u+1 u} (Type u) := 
{ equalizer := λ Y Z f g, { X := { y : Y // f y = g y }, ι := subtype.val } }

instance : has_pullbacks.{u+1 u} (Type u) := 
{ pullback := λ Y₁ Y₂ Z r₁ r₂, { X := { z : Y₁ × Y₂ // r₁ z.1 = r₂ z.2 }, π₁ := λ z, z.val.1, π₂ := λ z, z.val.2 } }

-- TODO update this stuff on colimits to the newer design:

instance : has_binary_coproducts.{u+1 u} (Type u) := 
{ coprod := λ Y Z, { X := Y ⊕ Z, ι₁ := sum.inl, ι₂ := sum.inr } }

-- TODO has_coproducts

local attribute [forward] cofork.w

instance : has_coequalizers.{u+1 u} (Type u) := 
{ coequalizer := λ Y Z f g, 
    begin
      letI setoid := eqv_gen.setoid (λ x y, ∃ a : Y, f a = x ∧ g a = y),
      exact { X := quotient setoid,
              π := by obviously }
    end,
  is_coequalizer := sorry }


variables {J : Type u} [𝒥 : small_category J]
include 𝒥

def limit (F : J ↝ Type u) : cone F :=
{ X := {u : Π j, F j // ∀ (j j' : J) (f : j ⟶ j'), F.map f (u j) = u j'},
  π := λ j u, u.val j }

def limit_is_limit (F : J ↝ Type u) : is_limit (limit F) :=
{ lift := λ s v, ⟨λ j, s.π j v, λ j j' f, congr_fun (s.w f) _⟩ }

instance : has_limits.{u+1 u} (Type u) :=
{ limit := @limit, is_limit := @limit_is_limit }

def colimit (F : J ↝ Type u) : cocone F :=
{ X := @quot (Σ j, F j) (λ p p', ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2),
  ι := λ j x, quot.mk _ ⟨j, x⟩,
  w := λ j j' f, funext $ λ x, eq.symm (quot.sound ⟨f, rfl⟩) }

local attribute [elab_with_expected_type] quot.lift
def colimit_is_colimit (F : J ↝ Type u) : is_colimit (colimit F) :=
{ desc := λ s, quot.lift (λ (p : Σ j, F j), s.ι p.1 p.2)
    (assume ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩,
      by rw hf; exact (congr_fun (s.w f) x).symm) }

instance : has_colimits.{u+1 u} (Type u) :=
{ colimit := @colimit, is_colimit := @colimit_is_colimit }

end category_theory.universal.types


