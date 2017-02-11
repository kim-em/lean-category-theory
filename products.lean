-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .category
import .functor
import .natural_transformation

-- set_option pp.universes true

open tqft.categories
open tqft.categories.functor

namespace tqft.categories.products

universe variables u v

@[reducible] definition ProductCategory (C : Category) (D : Category) :
  Category :=
  {
    Obj      := C^.Obj × D^.Obj,
    Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd)),
    identity := λ X, (C^.identity (X^.fst), D^.identity (X^.snd)),
    compose  := λ _ _ _ f g, (C^.compose (f^.fst) (g^.fst), D^.compose (f^.snd) (g^.snd)),

    left_identity  := begin
                        intros, simp,
                        induction f,
                        simp
                      end,
    right_identity := begin
                        intros, simp,
                        induction f,
                        simp
                      end,
    associativity  := begin
                        intros, 
                        rewrite [ C^.associativity, D^.associativity ]
                      end
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

definition ProductFunctor { A B C D : Category } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects := λ X, (F X^.fst, G X^.snd),
  onMorphisms := λ _ _ f, (F^.onMorphisms f^.fst, G^.onMorphisms f^.snd),
  identities := ♮,
  functoriality := ♮
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

@[reducible] definition SwitchProductCategory ( C D : Category ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X^.snd, X^.fst),
  onMorphisms   := λ _ _ f, (f^.snd, f^.fst),
  identities    := ♮,
  functoriality := ♮
}

lemma switch_twice_is_the_identity ( C D : Category ) : FunctorComposition ( SwitchProductCategory C D ) ( SwitchProductCategory D C ) = IdentityFunctor (C × D) :=
begin
  fapply Functors_pointwise_equal,
  begin
    intros X,
    blast,
    induction X,
    blast
  end,
  begin
    intros X Y f,
    blast,
    induction f,
    blast
  end
end

definition ProductCategoryAssociator ( C D E : Category.{ u v } ) : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, (X^.fst^.fst, (X^.fst^.snd, X^.snd)),
  onMorphisms   := λ _ _ f, (f^.fst^.fst, (f^.fst^.snd, f^.snd)),
  identities    := ♮,
  functoriality := ♮
}

end tqft.categories.products

