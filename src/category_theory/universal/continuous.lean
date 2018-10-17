-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.tactics.obviously

open category_theory.limits

namespace category_theory

universes u v
variables {C : Type u} [𝒞 : category.{u v} C] {D : Type u} [𝒟 : category.{u v} D]

section
include 𝒞 𝒟

class continuous (F : C ⥤ D) :=
(preserves_limits : ∀ {J : Type v} [small_category J] (G : J ⥤ C) (c : cone G) (L : is_limit c), is_limit ((cones.functoriality G F) c))

class cocontinuous (F : C ⥤ D) :=
(preserves_colimits : ∀ {J : Type v} [small_category J] (G : J ⥤ C) (c : cocone G) (L : is_colimit c), is_colimit ((cocones.functoriality G F) c))
end

section
include 𝒞
instance : continuous (functor.id C) :=
{ preserves_limits := λ J 𝒥 G c L,
    begin resetI, exact
      { lift := λ s, @is_limit.lift _ _ _ _ _ c L
          { X := s.X,
            π := s.π,
            w' := λ j j' f, by erw s.w }, -- We need to do a little work here because `G ⋙ (functor.id _) ≠ G`.
        uniq' := λ s m w,  @is_limit.uniq _ _ _ _ _ c L
          { X := s.X,
            π := s.π,
            w' := λ j j' f, by erw s.w } m w, }
    end }

end

-- instance HomFunctorPreservesLimits (a : A) : preserves_limits ((coyoneda A) a) := {
--     preserves := λ I D q, sorry
-- }

-- instance RepresentableFunctorPreservesLimits (F : A ⥤ (Type u)) [representable F] : preserves_limits F := sorry


-- PROJECT right adjoints are continuous

end category_theory

