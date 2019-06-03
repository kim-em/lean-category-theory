-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import category_theory.graphs.category

-- FIXME why do we need this here?
@[obviously] meta def obviously_4 := tactic.tidy { tactics := extended_tidy_tactics }

open category_theory
open category_theory.graphs

universes v₁ v₂ u₁ u₂

namespace category_theory.graphs

def paths (C : Type u₂) := C

instance paths_category (C : Type u₁) [graph.{v₁} C] : category.{(max u₁ v₁)+1} (paths C) :=
{ hom     := λ x y : C, path x y,
  id      := λ x, path.nil x,
  comp    := λ _ _ _ f g, concatenate_paths f g,
  comp_id' := begin
              tidy,
              induction f, -- PROJECT think about how to automate an inductive step. When can you be sure it's a good idea?
              obviously,
             end,
  assoc'  := begin
              tidy,
              induction f,
              obviously,
            end }.

instance paths_small_category (C : Type u₁) [graph.{u₁ u₁} C] : small_category (paths C) := graphs.paths_category C

variables {C : Type u₂} [𝒞 : category.{v₂} C] {G : Type u₁} [𝒢 : graph.{v₁} G]
include 𝒢 𝒞

@[simp] def path_to_morphism
  (H : graph_hom G C)
  : Π {X Y : G}, path X Y → ((H.onVertices X) ⟶ (H.onVertices Y))
| ._ ._ (path.nil Z)              := 𝟙 (H.onVertices Z)
| ._ ._ (@path.cons ._ _ _ _ _ e p) := (H.onEdges e) ≫ (path_to_morphism p)

@[simp] lemma path_to_morphism.comp (H : graph_hom G C) {X Y Z : paths G} (f : X ⟶ Y) (g : Y ⟶ Z) : path_to_morphism H (f ≫ g) = path_to_morphism H f ≫ path_to_morphism H g :=
begin
  induction f,
  obviously,
end

end category_theory.graphs

namespace category_theory.functor

open category_theory.graphs

variables {C : Type u₂} [𝒞 : category.{v₂} C] {G : Type u₁} [𝒢 : graph.{v₁} G]
include 𝒢 𝒞

-- PROJECT obtain this as the left adjoint to the forgetful functor.
@[simp] def of_graph_hom (H : graph_hom G C) : (paths G) ⥤ C :=
{ obj := λ X, (H.onVertices X),
  map := λ _ _ f, (path_to_morphism H f) }

end category_theory.functor