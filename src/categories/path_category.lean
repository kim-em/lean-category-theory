-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import .functor
import .graphs
import .graphs.category

open categories

namespace categories.graphs

universes u₁ u₂

def Path (C : Type u₁) : Type u₁ := C

instance PathCategory (C : Type u₁) [graph C] : category (Path C) :=
{
  Hom            := λ x y : C, path x y,
  identity       := λ x, path.nil x,
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

variable {G : Type u₁}
variable [graph G]
variable {C : Type u₂}
variable [category C]


definition {u v} path_to_morphism
  (H : graph_homomorphism G C)
  : Π {X Y : G}, path X Y → Hom (H.onVertices X) (H.onVertices Y) 
| ._ ._ (path.nil Z)              := 𝟙 (H.onVertices Z)
| ._ ._ (@path.cons ._ _ _ _ _ e p) := (H.onEdges e) >> (path_to_morphism p)
 
-- PROJECT obtain this as the left adjoint to the forgetful functor.
definition Functor.from_GraphHomomorphism (H : graph_homomorphism G C) : Functor (Path G) C :=
{
  onObjects     := H.onVertices,
  onMorphisms   := λ _ _ f, path_to_morphism H f,
  functoriality := begin
                     -- PROJECT automation
                     tidy,
                     induction f,
                     {
                       unfold concatenate_paths,
                       unfold path_to_morphism,
                       tidy,
                    },
                     {
                      let p := f_ih g,
                      unfold concatenate_paths,
                      unfold path_to_morphism,
                      tidy,
                      begin[smt] eblast end,
                    }
                   end
}

end categories.graphs
