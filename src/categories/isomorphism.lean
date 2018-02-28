-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category

open categories

namespace categories.isomorphism
universes u

variable {C : Type (u+1)}
variable [category C]
variables {X Y Z : C}

structure Isomorphism (X Y : C) :=
(morphism : X ⟶ Y)
(inverse : Y ⟶ X)
(witness_1 : morphism ≫ inverse = 𝟙 X . obviously)
(witness_2 : inverse ≫ morphism = 𝟙 Y . obviously)

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [simp,ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

infixr ` ≅ `:10  := Isomorphism             -- type as \cong

-- These lemmas are quite common, to help us avoid having to much around with associativity.
-- If anyone has a suggestion for automating them away, I would be very appreciative.
@[simp,ematch] lemma Isomorphism.witness_1_assoc_lemma (I : X ≅ Y) (f : X ⟶ Z) : I.morphism ≫ I.inverse ≫ f = f := ♯
@[simp,ematch] lemma Isomorphism.witness_2_assoc_lemma (I : X ≅ Y) (f : Y ⟶ Z) : I.inverse ≫ I.morphism ≫ f = f := ♯

instance Isomorphism_coercion_to_morphism : has_coe (X ≅ Y) (X ⟶ Y) :=
  {coe := Isomorphism.morphism}

definition IsomorphismComposition (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z :=
{
  morphism := α.morphism ≫ β.morphism,
  inverse := β.inverse ≫ α.inverse
}

@[applicable] lemma Isomorphism_pointwise_equal
  (α β : X ≅ Y)
  (w : α.morphism = β.morphism) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    simp at w,    
    have p : g = k,
      begin
        -- PROJECT why can't we automate this? -- why doesn't rewrite search work?
        tidy,
        resetI,
        rewrite ← @category.left_identity C _ _ _ k,
        rewrite ← wα2,
        rewrite category.associativity,
        simp *,
      end,
    smt_eblast
  end

definition Isomorphism.reverse (I : X ≅ Y) : Y ≅ X := {
  morphism  := I.inverse,
  inverse   := I.morphism
}

@[simp] lemma Isomorphism.cancel_morphism_left (I : X ≅ Y) (f g : Y ⟶ Z) : I.morphism ≫ f = I.morphism ≫ g ↔ f = g :=
begin
tidy,
have h := congr_arg (λ h, I.inverse ≫ h) a,
tidy,
end
@[simp] lemma Isomorphism.cancel_morphism_right (I : X ≅ Y) (f g : Z ⟶ X) : f ≫ I.morphism = g ≫ I.morphism ↔ f = g :=
begin
tidy,
have h := congr_arg (λ h, h ≫ I.inverse) a,
tidy,
end
@[simp] lemma Isomorphism.cancel_inverse_left (I : X ≅ Y) (f g : X ⟶ Z) : I.inverse ≫ f = I.inverse ≫ g ↔ f = g :=
begin
tidy,
have h := congr_arg (λ h, I.morphism ≫ h) a,
tidy,
end
@[simp] lemma Isomorphism.cancel_inverse_right (I : X ≅ Y) (f g : Z ⟶ Y) : f ≫ I.inverse = g ≫ I.inverse ↔ f = g :=
begin
tidy,
have h := congr_arg (λ h, h ≫ I.morphism) a,
tidy,
end

structure is_Isomorphism (morphism : X ⟶ Y) :=
(inverse : Y ⟶ X)
(witness_1 : morphism ≫ inverse = 𝟙 X . obviously)
(witness_2 : inverse ≫ morphism = 𝟙 Y . obviously)

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [simp,ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

instance is_Isomorphism_coercion_to_morphism (f : X ⟶ Y): has_coe (is_Isomorphism f) (X ⟶ Y) :=
  {coe := λ _, f}

definition Epimorphism (f : X ⟶ Y) := Π (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h
definition Monomorphism (f : X ⟶ Y) := Π (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h

end categories.isomorphism
