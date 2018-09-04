-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton, Mario Carneiro

import category_theory.limits.shape
import category_theory.filtered

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section terminal
class is_terminal (t : C) :=
(lift : ∀ (s : C), s ⟶ t)
(uniq' : ∀ (s : C) (m : s ⟶ t), m = lift s . obviously)

restate_axiom is_terminal.uniq'
attribute [search, back'] is_terminal.uniq

@[extensionality] lemma is_terminal.ext {X : C} (P Q : is_terminal.{u v} X) : P = Q := 
begin tactic.unfreeze_local_instances, cases P, cases Q, congr, obviously, end

end terminal

section initial
structure is_initial (t : C) :=
(desc : ∀ (s : C), t ⟶ s)
(uniq : ∀ (s : C) (m : t ⟶ s), m = desc s . obviously)

restate_axiom is_initial.uniq
attribute [search, back'] is_initial.uniq_lemma

@[extensionality] lemma is_initial.ext {X : C} (P Q : is_initial.{u v} X) : P = Q := 
begin cases P, cases Q, obviously, end

instance hom_to_initial_subsingleton (X' : C) (X : C) (B : is_initial.{u v} X') : subsingleton (X' ⟶ X) :=
begin
  fsplit, intros f g,
  rw B.uniq X f,
  rw B.uniq X g,
end

end initial

variable (C)

class has_terminal_object :=
(terminal    : C)
(is_terminal : is_terminal.{u v} terminal . obviously)

class has_initial_object :=
(initial    : C)
(is_initial : is_initial.{u v} initial . obviously)

def terminal_object [has_terminal_object.{u v} C] : C := has_terminal_object.terminal.{u v} C

variable {C}
section
variables [has_terminal_object.{u v} C] 

instance terminal_object.universal_property : is_terminal.{u v} (terminal_object.{u v} C) := 
has_terminal_object.is_terminal.{u v} C
def terminal_object.hom (X : C) : (X ⟶ terminal_object.{u v} C) := 
is_terminal.lift.{u v} (terminal_object.{u v} C) X

@[extensionality] lemma terminal.hom_ext {X' : C} (f g : X' ⟶ terminal_object.{u v} C) : f = g :=
begin
  rw is_terminal.uniq (terminal_object.{u v} C) X' f,
  rw is_terminal.uniq (terminal_object.{u v} C) X' g,
end
end

end category_theory.limits
