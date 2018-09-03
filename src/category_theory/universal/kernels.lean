import category_theory.universal.zero
import category_theory.over

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
attribute [simp,search] is_kernel.fac_lemma
restate_axiom is_kernel.uniq
attribute [search, back'] is_kernel.uniq_lemma

@[extensionality] lemma is_kernel.ext {f : Y ⟶ Z} {ι : X ⟶ Y} (P Q : is_kernel f ι) : P = Q :=
begin cases P, cases Q, obviously end

-- TODO should be marked [search]?
lemma kernel.w {f : Y ⟶ Z} {X : C} (ι : X ⟶ Y) (k : is_kernel f ι) : ι ≫ f = zero_morphism _ _ := by rw k.w

variable (C)

class has_kernels :=
(kernel : Π {Y Z : C} (f : Y ⟶ Z), C)
(ι       : Π {Y Z : C} (f : Y ⟶ Z), kernel f ⟶ Y)
(is     : Π {Y Z : C} (f : Y ⟶ Z), is_kernel f (ι f))

variable {C}

variable [has_kernels.{u v} C]

def kernel (f : Y ⟶ Z) : C := has_kernels.kernel.{u v} f
def kernel.ι (f : Y ⟶ Z) : kernel f ⟶ Y := has_kernels.ι.{u v} f
def kernel.subobject (f : Y ⟶ Z) : over Y := ⟨ kernel f, kernel.ι f ⟩

def kernel_of_equalizer {f : Y ⟶ Z} {t : fork f (zero_morphism _ _)} (e : is_equalizer t) : is_kernel f t.ι :=
{ w := begin have p := t.w_lemma, simp at p, exact p end,
  lift := λ X' ι' w, e.lift { X := X', ι := ι' },
  uniq := λ X' ι' w m h, begin tidy, apply e.uniq { X := X', ι := m ≫ t.ι }, tidy end }

def equalizer_of_kernel {f : Y ⟶ Z} {t : fork f (zero_morphism _ _)} (k : is_kernel f t.ι) : is_equalizer t :=
{ lift := λ s, begin have e := s.w_lemma, tidy, exact k.lift e, end, 
  uniq := sorry, }

def kernels_are_equalizers {f : Y ⟶ Z} (t : fork f (zero_morphism _ _)) : equiv (is_kernel f t.ι) (is_equalizer t) := 
{ to_fun  := equalizer_of_kernel,
  inv_fun := kernel_of_equalizer,
  left_inv  := sorry,
  right_inv := sorry }

end category_theory.universal

