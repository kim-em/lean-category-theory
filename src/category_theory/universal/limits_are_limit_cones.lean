import .cones

open category_theory

namespace category_theory.universal

universes u v
variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞 

variable {F : J ↝ C}

def limit_cone_of_limit (L : limit F) : limit_cone F :=
{ X := { X := L.t.X,
         π := L.t.π },
  h := { lift := λ s, { hom := L.h.lift s, },
         uniq := begin tidy, apply L.h.uniq_lemma, tidy, end } } -- uniq_lemma is marked @[back'], but the unifier fails to apply it

def limit_of_limit_cone (L : limit_cone F) : limit F :=
{ X := L.X.X,
  π := L.X.π,
  h := { lift := λ s, (L.h.lift s).hom,
         uniq := begin tidy, have p := L.h.uniq_lemma s { hom := m, w := w }, rw ← p, end } } 

-- We now prove some `evil` extensionality lemmas; we're about to prove an evil theorem anyway.

lemma point.ext (c d : point C) (h : c.X = d.X) : c = d :=
begin cases c, cases d, obviously end

lemma cone.ext {C : Type u} [𝒞 : category.{u v} C] {J : Type v} [small_category J] {F : J ↝ C} (c d : cone F) (h_X : c.X = d.X) (h_π : ∀ j, c.π j = (eq_to_iso h_X).hom ≫ d.π j) : c = d :=
begin
  cases c, cases d,
  cases c__to_shape, cases d__to_shape,
  dsimp at h_X,
  subst h_X,
  congr,
  tidy,
end

lemma terminal_object.ext (P Q : terminal_object.{u v} C) (h : P.t = Q.t) : P = Q :=
begin cases P, cases Q, obviously, cases P__t, cases Q__t, obviously, apply is_terminal.ext end

lemma limit.ext {F : J ↝ C} (P Q : limit F) (h : P.t = Q.t) : P = Q := 
begin cases P, cases Q, obviously, cases P__t, cases Q__t, obviously, apply is_limit.ext, end

local attribute [extensionality] point.ext cone.ext terminal_object.ext limit.ext

def limits_are_limit_cones : equiv (limit F) (limit_cone F) :=
{ to_fun    := limit_cone_of_limit,
  inv_fun   := limit_of_limit_cone,
  left_inv  := begin
                 obviously, 
                 intros,
                 cases x, cases x__t,
                 tidy, 
               end,
  right_inv := begin 
                 tidy, 
                 unfold limit_cone_of_limit, 
                 tidy,
               end }

end category_theory.universal
