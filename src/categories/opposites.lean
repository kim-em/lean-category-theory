-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .functor
import .products
import .types

open categories
open categories.functor
open categories.products
open categories.types

namespace categories.opposites

universes u₁ u₂

inductive op (C : Type u₁) : Type u₁
| op : C → op

notation C `ᵒᵖ` := op C

variable {C : Type u₁}
variable [category C]
variable {D : Type u₂}
variable [category D]

def op.of : Cᵒᵖ  → C
| (op.op X) := X

#print op.of

instance opposite_coercion_1 : has_coe (Cᵒᵖ) C :=
  {coe := op.of}
instance opposite_coercion_2 : has_coe C (Cᵒᵖ) :=
  {coe := op.op}

instance Opposite : category (Cᵒᵖ):=
{
    Hom := λ X Y : Cᵒᵖ, Hom (Y : C) (X : C),
    compose  := λ _ _ _ f g, g >> f,
    identity := λ X, 𝟙 X
}


instance opposite_coercion_3 (X Y : C) : has_coe (Hom X Y) (@Hom (Cᵒᵖ) _ Y X) :=
  {coe := id}
instance opposite_coercion_4 (X Y : (Cᵒᵖ)) : has_coe (Hom X Y) (@Hom C _ Y X) :=
  {coe := id}

definition OppositeFunctor (F : Functor C D) : Functor (Cᵒᵖ) (Dᵒᵖ) :=
{
  onObjects     := λ X, F.onObjects X,
  onMorphisms   := λ X Y f, F.onMorphisms f
}

definition HomPairing {C : Type u₁} [C_cat : category C]: Functor ((Cᵒᵖ) × C) (Type u₁) :=
{
  onObjects     := λ p, @Hom C _ p.1 p.2,
  onMorphisms   := λ X Y f,
                   begin
                     tidy,
                     induction f,
                     tidy,
                     induction Y_fst,
                     induction X_fst,
                     unfold op.of,
                     unfold op.of at a,
                     exact f_fst >> a >> f_snd
                   end
  --λ X Y f, λ g : @Hom C _ X.1 X.2, (@category.compose _ C_cat _ _ _ (@category.compose _ C_cat _ _ _ (f.1 : @Hom C _ Y.1 X.1)  (g : @Hom C _ X.1 X.2)) (f.2 : @Hom C _ X.2 Y.2))
}

-- PROJECT prove C^op^op is C
-- definition OppositeOpposite (C : Category) : Equivalence (Opposite (Opposite C)) C := sorry
-- PROJECT opposites preserve products, functors, slices.

local attribute [reducible] Opposite

@[simp,ematch] lemma ContravariantFunctor.functoriality
  {C : Category}
  {D : Category}
  {F : Functor (Opposite C) D}
  {X Y Z : C.Obj}
  {f : C.Hom X Y} {g : C.Hom Y Z} :
    F.onMorphisms (C.compose f g) = D.compose (F.onMorphisms g) (F.onMorphisms f) := ♮ 

@[simp,ematch] lemma ContravariantFunctor.identities
  {C : Category}
  {D : Category}
  {F : Functor (Opposite C) D}
  {X : C.Obj} :
    F.onMorphisms (C.identity X) = D.identity (F.onObjects X) := ♮

end categories.opposites