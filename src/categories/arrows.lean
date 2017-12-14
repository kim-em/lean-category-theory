-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation

open categories
open categories.functor
open categories.natural_transformation

namespace categories.arrows

local attribute [applicable] Category.identity -- This says that whenever there is a goal of the form C.Hom X X, we can safely complete it with the identity morphism. This isn't universally true.

-- Is there any point defining these separately (rather than as the functor category from the walking arrow)?

definition Arrows ( C : Category ) : Category :=
{
  Obj := Σ (p : C.Obj × C.Obj), C.Hom p.1 p.2,
  Hom := λ X Y, { f : (C.Hom X.1.1 Y.1.1 × C.Hom X.1.2 Y.1.2) // C.compose f.1 Y.2 = C.compose X.2 f.2 },
  identity       := by tidy,
  compose        := λ _ _ _ f g, ⟨ (C.compose f.val.1 g.val.1, C.compose f.val.2 g.val.2), ♯ ⟩ ,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition Arrows_Functor { C D : Category } ( F : Functor C D ) : Functor (Arrows C) (Arrows D) :=
{
  onObjects     := λ X, ⟨ (F.onObjects X.1.1, F.onObjects X.1.2), F.onMorphisms X.2 ⟩,
  onMorphisms   := λ _ _ f, ⟨ (F.onMorphisms f.val.1, F.onMorphisms f.val.2), ♯ ⟩,
  identities    := ♯,
  functoriality := ♯
}

definition Arrows_Natural_Transformation { C D : Category } { F G : Functor C D } ( τ : NaturalTransformation F G ) : NaturalTransformation (Arrows_Functor F) (Arrows_Functor G) :=
{
  components := λ X, ⟨ ( τ.components X.1.1, τ.components X.1.2 ), ♯ ⟩,
  naturality := ♯ 
}

end categories.arrows
