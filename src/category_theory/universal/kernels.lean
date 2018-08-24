import .zero

open category_theory

universes u v

namespace category_theory.universal

variables {C : Type u} [𝒞 : category.{u v} C] [has_zero_object.{u v} C]
include 𝒞
variables {X Y Z : C}

structure is_kernel (f : Y ⟶ Z) (ι : X ⟶ Y) :=
(w    : ι ≫ f = zero_morphism _ _)
(lift : Π {X' : C} {ι' : X' ⟶ Y} (w : ι' ≫ f = zero_morphism X' Z), X' ⟶ X)
(fac  : Π {X' : C} {ι' : X' ⟶ Y} (w : ι' ≫ f = zero_morphism X' Z), (lift w) ≫ ι = ι' . obviously)
(uniq : Π {X' : C} {ι' : X' ⟶ Y} (w : ι' ≫ f = zero_morphism X' Z) {m : X' ⟶ X} (h : m ≫ ι = ι'), m = lift w . obviously)

restate_axiom is_kernel.fac
attribute [simp,ematch] is_kernel.fac_lemma
restate_axiom is_kernel.uniq
attribute [ematch, back'] is_kernel.uniq_lemma

@[extensionality] lemma is_kernel.ext {f : Y ⟶ Z} {ι : X ⟶ Y} (P Q : is_kernel f ι) : P = Q :=
begin cases P, cases Q, obviously end

structure kernel (f : Y ⟶ Z) :=
(X : C)
(ι : X ⟶ Y)
(h : is_kernel f ι)

@[simp,ematch] lemma kernel.w {f : Y ⟶ Z} (k : kernel f) : k.ι ≫ f = zero_morphism _ _ := by rw k.h.w

variable (C)

class has_kernels :=
(kernel : Π {Y Z : C} (f : Y ⟶ Z), kernel.{u v} f)

variable {C}

variable [has_kernels.{u v} C]

def kernel' (f : Y ⟶ Z) := has_kernels.kernel.{u v} f


def kernel_of_equalizer {f : Y ⟶ Z} (e : equalizer f (zero_morphism _ _)) : kernel f :=
{ X := e.X,
  ι := e.ι,
  h := { w := begin have p := e.t.w_lemma, simp at p, exact p end,
         lift := λ X' ι' w, e.h.lift { X := X', ι := ι' },
         uniq := λ X' ι' w m h, begin tidy, apply e.h.uniq { X := X', ι := m ≫ (e.t).ι }, tidy end } }

def equalizer_of_kernel {f : Y ⟶ Z} (k : kernel f) : equalizer f (zero_morphism _ _) :=
{ X := k.X,
  ι := k.ι,
  h := { lift := λ s, begin have e := s.w_lemma, tidy, exact k.h.lift e, end, 
         uniq := sorry, }
}

lemma kernel.ext (f : Y ⟶ Z) (k k' : kernel f) (h_X : k.X = k'.X) (h_ι : k.ι = (eq_to_iso h_X).hom ≫ k'.ι) : k = k' :=
begin cases k, cases k', obviously, cases k_h, cases k'_h, obviously, end

local attribute [extensionality] kernel.ext

def kernels_are_equalizers {f : Y ⟶ Z} : equiv (kernel f) (equalizer f (zero_morphism _ _)) := 
{ to_fun  := equalizer_of_kernel,
  inv_fun := kernel_of_equalizer,
  left_inv  := sorry,
  right_inv := sorry }


end category_theory.universal

