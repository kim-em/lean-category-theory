-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import categories.functor
import categories.graphs
import categories.graphs.category
import categories.universe_lifting

open categories

namespace categories.graphs

universes u₁ u₂

@[reducible] def Path (C : Type (u₁+1)) : Type (u₁+2) := ulift.{u₁+2} C

instance PathCategory (C : Type (u₁+1)) [graph C] : category (Path C) :=
{
  Hom            := λ x y : Path C, path x.down y.down,
  identity       := λ x, path.nil x.down,
  compose        := λ _ _ _ f g, concatenate_paths f g,
  right_identity := begin
                      tidy,
                      induction f,
                      {
                        -- when f is nil
                        trivial,
                      },
                      {
                        -- when f is cons
                        exact congr_arg (λ p, path.cons f_e p) f_ih
                      }
                    end,
  associativity  := begin
                      tidy,
                      induction f,
                      {
                        -- when f is nil
                        trivial,
                      },
                      {
                        -- when f is cons
                        exact congr_arg (λ p, path.cons f_e p) (f_ih g)
                      }
                    end
}

open categories.functor

variable {G : Type (u₁+1)}
variable [graph G]
variable {C : Type (u₂+1)}
variable [category C]

definition path_to_morphism
  (H : graph_homomorphism G C)
  : Π {X Y : G}, path X Y → ((H.onVertices X) ⟶ (H.onVertices Y))
| ._ ._ (path.nil Z)              := 𝟙 (H.onVertices Z)
| ._ ._ (@path.cons ._ _ _ _ _ e p) := (H.onEdges e) ≫ (path_to_morphism p)
 
@[simp] lemma path_to_morphism.comp   (H : graph_homomorphism G C) {X Y Z : G} (f : path X Y) (g : path Y Z): path_to_morphism H (graphs.concatenate_paths f g) = path_to_morphism H f ≫ path_to_morphism H g :=
begin
induction f,
{
  tidy,
},
{
  let p := f_ih g,
  tidy,
}
end

-- FIXME
-- PROJECT obtain this as the left adjoint to the forgetful functor.
-- definition Functor.from_GraphHomomorphism (H : graph_homomorphism G C) : Functor (Path G) (ulift.{u₁+2} C) :=
-- { onObjects     := λ X, ulift.up (H.onVertices X.down),
--   onMorphisms   := λ _ _ f, ulift.up (path_to_morphism H f), }

end categories.graphs
