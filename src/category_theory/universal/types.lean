import category_theory.universal.limits
import category_theory.universal.colimits
import category_theory.universal.limits.limits

universe u

open category_theory category_theory.universal

namespace category_theory.universal.types

local attribute [forward] fork.w square.w

instance : has_terminal_object.{u+1 u} (Type u) :=
{ terminal := punit }

instance : has_binary_products.{u+1 u} (Type u) := 
{ prod := λ Y Z, { X := Y × Z, π₁ := prod.fst, π₂ := prod.snd } }

@[simp] lemma types_prod (Y Z : Type u) : universal.prod Y Z = (Y × Z) := rfl

instance : has_products.{u+1 u} (Type u) := 
{ prod := λ β f, { X := Π b, f b, π := λ b x, x b } }.

@[simp] lemma types_pi {β : Type u} (f : β → Type u) : pi f = Π b, f b := rfl
@[simp] lemma types_pi_π {β : Type u} (f : β → Type u) (b : β) : pi.π f b = λ (g : Π b, f b), g b := rfl.
@[simp] lemma types_pi_map {β α : Type u} (f : α → Type u) (g : β → Type u) 
  (h : β → α) (k : Π b, f (h b) ⟶ g b) (a : pi f) : 
  pi.map h k a = (λ (b : β), k b (a (h b))) := rfl
@[simp] lemma types_pi_of_components {β : Type u} (f : β → Type u) {P : Type u} (p : Π b, P ⟶ f b) : 
  pi.of_components p = λ q b, p b q := rfl

instance : has_equalizers.{u+1 u} (Type u) := 
{ equalizer := λ Y Z f g, { X := { y : Y // f y = g y }, ι := subtype.val } }

instance : has_pullbacks.{u+1 u} (Type u) := 
{ pullback := λ Y₁ Y₂ Z r₁ r₂, { X := { z : Y₁ × Y₂ // r₁ z.1 = r₂ z.2 }, π₁ := λ z, z.val.1, π₂ := λ z, z.val.2 } }

local attribute [elab_with_expected_type] quot.lift

instance : has_initial_object.{u+1 u} (Type u) :=
{ initial := pempty }

instance : has_binary_coproducts.{u+1 u} (Type u) := 
{ coprod := λ Y Z, { X := Y ⊕ Z, ι₁ := sum.inl, ι₂ := sum.inr } }

instance : has_coproducts.{u+1 u} (Type u) := 
{ coprod := λ β f, { X := Σ b, f b, ι := λ b x, ⟨b, x⟩ } }

def pushout {Y₁ Y₂ Z : Type u} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) : cosquare r₁ r₂ :=
{ X := @quot (Y₁ ⊕ Y₂) (λ p p', ∃ z : Z, p = sum.inl (r₁ z) ∧ p' = sum.inr (r₂ z) ),
  ι₁ := λ o, quot.mk _ (sum.inl o),
  ι₂ := λ o, quot.mk _ (sum.inr o),
  w := funext $ λ z, quot.sound ⟨ z, by tidy ⟩, }.

def pushout_is_pushout {Y₁ Y₂ Z : Type u} (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) : is_pushout (pushout r₁ r₂) :=
{ desc := λ s, quot.lift (λ o, sum.cases_on o s.ι₁ s.ι₂)
            (assume o o' ⟨z, hz⟩, begin rw hz.left, rw hz.right, dsimp, exact congr_fun s.w z end) }

instance : has_pushouts.{u+1 u} (Type u) :=
{ pushout := @pushout, is_pushout := @pushout_is_pushout }

def coequalizer {Y Z : Type u} (f g : Y ⟶ Z) : cofork f g :=
{ X := @quot Z (λ z z', ∃ y : Y, z = f y ∧ z' = g y),
  π := λ z, quot.mk _ z,
  w := funext $ λ x, quot.sound ⟨ x, by tidy ⟩ }.

def coequalizer_is_coequalizer {Y Z : Type u} (f g : Y ⟶ Z) : is_coequalizer (coequalizer f g) :=
{ desc := λ s, quot.lift (λ (z : Z), s.π z)
    (assume z z' ⟨y, hy⟩, begin rw hy.left, rw hy.right, exact congr_fun s.w y, end) }

instance : has_coequalizers.{u+1 u} (Type u) := 
{ coequalizer := @coequalizer, is_coequalizer := @coequalizer_is_coequalizer }

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

def colimit_is_colimit (F : J ↝ Type u) : is_colimit (colimit F) :=
{ desc := λ s, quot.lift (λ (p : Σ j, F j), s.ι p.1 p.2)
    (assume ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩,
      by rw hf; exact (congr_fun (s.w f) x).symm) }

instance : has_colimits.{u+1 u} (Type u) :=
{ colimit := @colimit, is_colimit := @colimit_is_colimit }

end category_theory.universal.types


