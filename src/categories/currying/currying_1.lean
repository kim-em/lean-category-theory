-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import ..natural_transformation
import ..equivalence
import ..products.bifunctors

open categories
open categories.isomorphism
open categories.functor
open categories.equivalence
open categories.functor_categories

namespace categories.natural_transformation

universes u₁ u₂ u₃

variables (C : Type (u₁+1)) [category C] (D : Type (u₂+1)) [category D] (E : Type (u₃+1)) [category E]

definition uncurry_functor_objects (F : C ↝ (D ↝ E)) : (C × D) ↝ E := {
  onObjects     := λ X, (F X.1) X.2,
  onMorphisms   := λ X Y f, ((F &> f.1).components X.2) ≫ ((F Y.1) &> f.2)
}
definition uncurry_functor_morphisms (F G : C ↝ (D ↝ E)) (T : F ⟹ G): (uncurry_functor_objects C D E F) ⟹ (uncurry_functor_objects C D E G) := {
  components := λ X, (T.components _).components _
}

definition Uncurry_Functors : (C ↝ (D ↝ E)) ↝ ((C × D) ↝ E) := {
  onObjects     := uncurry_functor_objects C D E,
  onMorphisms   := uncurry_functor_morphisms C D E, 
}

definition curry_functor (F : (C × D) ↝ E) (X : C) : D ↝ E := {
  onObjects     := λ Y, F (X, Y),
  onMorphisms   := λ Y Y' g, F &> (𝟙 X, g),
}
definition curry_functor' (F : (C × D) ↝ E) (X X' : C) (f : X ⟶ X') : (curry_functor C D E F X) ⟹ (curry_functor C D E F X') := {
  components := λ Y, F.onMorphisms (f, 𝟙 Y),
}
definition curry_functor_objects (F : (C × D) ↝ E) : C ↝ (D ↝ E) := {
  onObjects     := λ X, curry_functor C D E F X,
  onMorphisms   := λ X X' f, curry_functor' C D E F X X' f,
}

definition curry_functor_morphisms (F G : (C × D) ↝ E) (T : F ⟹ G) : (curry_functor_objects C D E F) ⟹ (curry_functor_objects C D E G) := {
  components := λ X, {
    components := λ Y, T.components (X, Y),
  },
}


definition Curry_Functors : ((C × D) ↝ E) ↝ (C ↝ (D ↝ E)) := {
  onObjects     := curry_functor_objects C D E,
  onMorphisms   := curry_functor_morphisms C D E,
}

end categories.natural_transformation