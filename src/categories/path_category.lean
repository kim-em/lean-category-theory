-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import categories.functor
import categories.graphs
import categories.graphs.category
import categories.universe_lifting

open category_theory
open category_theory.graphs

universes u₁ u₂

variable {G : Type u₁}
variable [graph G]
variable {C : Type u₂}
variable [small_category C]

namespace category_theory.graphs

def Path (C : Type u₁) := C 

@[reducible] instance PathCategory (C : Type u₁) [graph C] : small_category (Path C) :=
{
  Hom            := λ x y : C, path x y,
  identity       := λ x, path.nil x,
  compose        := λ _ _ _ f g, concatenate_paths f g,
  right_identity := begin
                      tidy,
                      induction f, -- PROJECT think about how to automate an inductive step. When can you be sure it's a good idea?
                      obviously,                      
                    end,
  associativity  := begin
                      tidy,
                      induction f,
                      obviously,                    
                    end
}

definition path_to_morphism
  (H : graph_homomorphism G C)
  : Π {X Y : G}, path X Y → ((H.onVertices X) ⟶ (H.onVertices Y))
| ._ ._ (path.nil Z)              := 𝟙 (H.onVertices Z)
| ._ ._ (@path.cons ._ _ _ _ _ e p) := (H.onEdges e) ≫ (path_to_morphism p)
 
@[simp] lemma path_to_morphism.comp (H : graph_homomorphism G C) {X Y Z : G} (f : path X Y) (g : path Y Z): path_to_morphism H (graphs.concatenate_paths f g) = path_to_morphism H f ≫ path_to_morphism H g :=
begin
  induction f,
  obviously,
end

end category_theory.graphs

namespace category_theory.Functor

open category_theory.graphs

-- PROJECT obtain this as the left adjoint to the forgetful functor.
definition from_GraphHomomorphism (H : graph_homomorphism G C) : Functor (Path G) C :=
{ onObjects     := λ X, (H.onVertices X),
  onMorphisms   := λ _ _ f, (path_to_morphism H f) }

end category_theory.Functor