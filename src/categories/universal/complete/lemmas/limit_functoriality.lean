-- -- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- -- Released under Apache 2.0 license as described in the file LICENSE.
-- -- Authors: Scott Morrison

-- import ...instances

-- open categories
-- open categories.functor
-- open categories.natural_transformation
-- open categories.functor_categories
-- open categories.isomorphism
-- open categories.products
-- open categories.initial
-- open categories.types
-- open categories.util
-- open categories.universal

-- namespace categories.universal.lemmas.limit_functoriality

-- @[applicable] private lemma {u v} uniqueness_of_morphism_to_limit
--   {J C : Category.{u v}}
--   {F : Functor J C}
--   {L : LimitCone F}
--   {X : Cone F}
--   {g : C.Hom X.cone_point L.terminal_object.cone_point}
--   (w : ∀ j : J.Obj, C.compose g ((L.terminal_object).cone_maps j) = X.cone_maps j)
--     : (L.morphism_to_terminal_object_from X).cone_morphism = g :=
--   begin
--     let G : (Cones F).Hom X L.terminal_object := ⟨ g, w ⟩,
--     have q := L.uniqueness_of_morphisms_to_terminal_object _ (L.morphism_to_terminal_object_from X) G,
--     exact congr_arg ConeMorphism.cone_morphism q,
--   end

-- @[simp,ematch] private lemma {u v} morphism_to_terminal_object_composed_with_cone_map
--   {J C : Category.{u v}}
--   {F : Functor J C}
--   {L : LimitCone F}
--   {X : Cone F}
--   {j : J.Obj}
--     : C.compose (L.morphism_to_terminal_object_from X).cone_morphism (L.terminal_object.cone_maps j) = X.cone_maps j :=
--   (L.morphism_to_terminal_object_from X).commutativity j

-- @[applicable,reducible] definition morphism_to_terminal_object_cone_point 
--   {J D : Category}
--   {Z : D.Obj}
--   {G : Functor J D}
--   {L : LimitCone G}
--   (cone_maps : Π j : J.Obj, D.Hom Z (G.onObjects j)) 
--   (commutativity : Π j k : J.Obj, Π f : J.Hom j k, D.compose (cone_maps j) (G.onMorphisms f) = cone_maps k)
--    : D.Hom Z L.terminal_object.cone_point :=
-- begin
--   let cone : Cone G := {
--     cone_point    := Z,
--     cone_maps     := cone_maps,
--     commutativity := commutativity
--  },
--   exact (L.morphism_to_terminal_object_from cone).cone_morphism, 
-- end

-- @[applicable] private lemma {u v} uniqueness_of_morphism_from_colimit
--   {J C : Category.{u v}}
--   {F : Functor J C}
--   {L : ColimitCocone F}
--   {X : Cocone F}
--   {g : C.Hom L.initial_object.cocone_point X.cocone_point}
--   (w : ∀ j : J.Obj, C.compose ((L.initial_object).cocone_maps j) g = X.cocone_maps j)
--     : (L.morphism_from_initial_object_to X).cocone_morphism = g :=
--   begin
--     let G : (Cocones F).Hom L.initial_object X := ⟨ g, w ⟩,
--     have q := L.uniqueness_of_morphisms_from_initial_object _ (L.morphism_from_initial_object_to X) G,
--     exact congr_arg CoconeMorphism.cocone_morphism q,
--   end

-- @[simp,ematch] private lemma {u v} cocone_map_composed_with_morphism_from_initial_object
--   {J C : Category.{u v}}
--   {F : Functor J C}
--   {L : ColimitCocone F}
--   {X : Cocone F}
--   {j : J.Obj}
--     : C.compose (L.initial_object.cocone_maps j) (L.morphism_from_initial_object_to X).cocone_morphism = X.cocone_maps j :=
--   (L.morphism_from_initial_object_to X).commutativity j

-- @[applicable] definition morphism_from_initial_object_cocone_point 
--   {J D : Category}
--   {Z : D.Obj}
--   {G : Functor J D}
--   {L : ColimitCocone G}
--   (cocone_maps : Π j : J.Obj, D.Hom (G.onObjects j) Z) 
--   (commutativity : Π j k : J.Obj, Π f : J.Hom j k, D.compose (G.onMorphisms f) (cocone_maps k) = cocone_maps j)
--    : D.Hom L.initial_object.cocone_point Z :=
-- begin
--   let cocone : Cocone G := {
--     cocone_point  := Z,
--     cocone_maps   := cocone_maps,
--     commutativity := commutativity
--  },
--   exact (L.morphism_from_initial_object_to cocone).cocone_morphism, 
-- end

-- end categories.universal.lemmas.limit_functoriality
