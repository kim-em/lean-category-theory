-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import .natural_transformation

-- set_option pp.universes true

open tqft.categories
open tqft.categories.functor
open tqft.categories.natural_transformation

namespace tqft.categories.products

universe variables u1 v1 u2 v2 u3 v3

@[reducible] definition ProductCategory (C : Category.{u1 v1}) (D : Category.{u2 v2}) :
  Category :=
  {
    Obj      := C^.Obj × D^.Obj,
    Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd)),
    identity := λ X, (C^.identity (X^.fst), D^.identity (X^.snd)),
    compose  := λ _ _ _ f g, (C^.compose (f^.fst) (g^.fst), D^.compose (f^.snd) (g^.snd)),

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := begin
                        abstract {
                          blast,
                          begin[smt]
                            eblast_using [ Category.associativity ]
                          end
                        }
                      end
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

@[reducible] definition LeftInjectionAt { D : Category.{u2 v2} } ( Z : D^.Obj ) ( C : Category.{u1 v1} ) : Functor C (C × D) :=
{ onObjects   := λ X, (X, Z),
  onMorphisms := λ X Y f, (f, D^.identity Z),
  identities  := ♮,
  functoriality := ♮
}

@[reducible] definition RightInjectionAt { C : Category.{u1 v1} } ( Z : C^.Obj) ( D : Category.{u2 v2} ) : Functor D (C × D) :=
{ onObjects   := λ X, (Z, X),
  onMorphisms := λ X Y f, (C^.identity Z, f),
  identities  := ♮,
  functoriality := ♮
}

@[reducible] definition ProductFunctor { A B C D : Category } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects     := λ X, (F X^.fst, G X^.snd),
  onMorphisms   := λ _ _ f, (F^.onMorphisms f^.fst, G^.onMorphisms f^.snd),
  identities    := ♮,
  functoriality := ♮
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

@[reducible] definition ProductNaturalTransformation { A B C D : Category } { F G : Functor A B } { H I : Functor C D } (α : NaturalTransformation F G) (β : NaturalTransformation H I) : NaturalTransformation (F × H) (G × I) :=
{
  components := λ X, (α X^.fst, β X^.snd),
  naturality :=
  begin
    abstract {
      blast,
      begin[smt]
        eblast_using [ NaturalTransformation.naturality ]
      end
    }
  end
}

namespace ProductNaturalTransformation
  notation α `×` β := ProductNaturalTransformation α β
end ProductNaturalTransformation

@[reducible] definition SwitchProductCategory ( C D : Category ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X^.snd, X^.fst),
  onMorphisms   := λ _ _ f, (f^.snd, f^.fst),
  identities    := ♮,
  functoriality := ♮
}

lemma switch_twice_is_the_identity ( C D : Category ) : FunctorComposition ( SwitchProductCategory C D ) ( SwitchProductCategory D C ) = IdentityFunctor (C × D) := ♮

@[reducible] definition ProductCategoryAssociator
  ( C : Category.{ u1 v1 } )
  ( D : Category.{ u2 v2 } )
  ( E : Category.{ u3 v3 } )
  : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, (X^.fst^.fst, (X^.fst^.snd, X^.snd)),
  onMorphisms   := λ _ _ f, (f^.fst^.fst, (f^.fst^.snd, f^.snd)),
  identities    := ♮,
  functoriality := ♮
}


end tqft.categories.products
