-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison


import categories.functor

open categories

namespace categories.functor

universes u₁ u₂

variable {C : Type (u₁+1)}
variable [large_category C]
variable {D : Type (u₂+1)}
variable [large_category D]

-- TODO this is WIP
class Functorial (f : C → D) :=
  (onMorphisms   : Π {X Y : C}, (X ⟶ Y) → ((f X) ⟶ (f Y)))
  (identities    : ∀ (X : C), onMorphisms (𝟙 X) = 𝟙 (f X) . obviously)
  (functoriality : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g) . obviously)

make_lemma Functorial.identities
make_lemma Functorial.functoriality
attribute [simp,ematch] Functorial.functoriality_lemma Functorial.identities_lemma

instance (F : C ↝ D) : Functorial (F.onObjects) := 
{ onMorphisms := F.onMorphisms }

-- TODO notations?
end categories.functor