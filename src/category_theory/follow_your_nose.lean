import category_theory.natural_transformation
import category_theory.opposites
import category_theory.types

import category_theory.tactics.obviously

universes v₁ u₁

open tactic

def fyn_names :=
[ `category_theory.category.id,
  `category_theory.functor.map,
  `category_theory.nat_trans.app,
  `category_theory.category.comp,
  `prod.mk ]

meta def construct_morphism : tactic unit :=
do ctx ← local_context,
   extra ← fyn_names.mmap (λ n, mk_const n),
   solve_by_elim { assumptions := return (ctx ++ extra) }

meta def fyn := tidy { tactics := tactic.tidy.default_tactics ++ [construct_morphism >> pure "construct_morphism"] }

attribute [tidy] construct_morphism

notation `ƛ` binders `, ` r:(scoped f, { category_theory.functor . obj := f, map := by obviously }) := r

open category_theory

variables (C : Type u₁) [𝒞 : category.{v₁+1} C]
include 𝒞

def yoneda : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁)) := ƛ X, ƛ Y : Cᵒᵖ, (unop Y) ⟶ X.

variables (D : Type u₁) [𝒟 : category.{v₁} D]
include 𝒟

def curry_id : C ⥤ (D ⥤ (C × D)) := ƛ X, ƛ Y, (X, Y)
