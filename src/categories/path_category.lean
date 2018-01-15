-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan and Scott Morrison

import .functor
import .graphs

open categories

namespace categories.graphs

definition PathCategory ( G : Graph ) : Category :=
{
  Obj            := G.Obj,
  Hom            := λ x y, path x y,
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

definition {u v} path_to_morphism
  { G : Graph.{u v} }
  { C : Category.{u v} }
  ( H : GraphHomomorphism G C.graph )
  : Π { X Y : G.Obj }, path X Y → C.Hom (H.onObjects X) (H.onObjects Y) 
| ._ ._ (path.nil Z)              := C.identity (H.onObjects Z)
| ._ ._ (@path.cons ._ _ _ _ e p) := C.compose (H.onMorphisms e) (path_to_morphism p)
 
-- PROJECT obtain this as the left adjoint to the forgetful functor.
definition Functor.from_GraphHomomorphism { G : Graph } { C : Category } ( H : GraphHomomorphism G C.graph ) : Functor (PathCategory G) C :=
{
  onObjects     := H.onObjects,
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
                      blast,
                     }
                   end
}

instance GraphHomomorphism_to_Functor_coercion { G : Graph } { C : Category }: has_coe (GraphHomomorphism G C.graph) (Functor (PathCategory G) C) :=
  { coe := Functor.from_GraphHomomorphism }

end categories.graphs
