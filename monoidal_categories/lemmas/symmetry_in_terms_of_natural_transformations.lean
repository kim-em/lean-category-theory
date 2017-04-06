-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison
import ..braided_monoidal_category

open tqft.categories
open tqft.categories.functor
open tqft.categories.products
open tqft.categories.natural_transformation
open tqft.categories.monoidal_category

namespace tqft.categories.braided_monoidal_category

-- universe variables u v

definition {u v} transport {A : Type u} { P : A → Type v} {x y : A} (p : x = y)
(u : P x) : P y :=
by induction p; exact u

definition {u v w} apdt011 
  {A : Type u} {Z : Type w} 
  {B : A → Type v} 
  (f : Πa, B a → Z) 
  {a a' : A} 
  {b : B a} 
  {b' : B a'} 
  (Ha : a = a') 
  (Hb : transport Ha b = b')
      : f a b = f a' b' :=
by cases Ha; cases Hb; reflexivity

set_option trace.check true

@[reducible] definition {u v} squared_Braiding { C : Category.{u v} } { m : MonoidalStructure C } ( commutor : Commutor m )
  : NaturalTransformation m.tensor m.tensor :=
  begin
    pose square := vertical_composition_of_NaturalTransformations commutor.morphism (whisker_on_left (SwitchProductCategory C C) commutor.morphism),
    refine ( cast _ square ),
    -- refine ( transport _ square ),
    rewrite - FunctorComposition.associativity,
    erewrite switch_twice_is_the_identity,
    rewrite FunctorComposition.left_identity,
  end 

-- set_option pp.implicit true
#check NaturalTransformation.components
-- @NaturalTransformation.components ?M_1 ?M_2 ?M_3 ?M_4 :
--   @NaturalTransformation ?M_1 ?M_2 ?M_3 ?M_4 → Π (X : ?M_1.Obj), ?M_2.Hom (⇑?M_3 X) (⇑?M_4 X)

-- α === Type (max u v)
-- a === (@NaturalTransformation (C × C) C (@MonoidalStructure.tensor C m)
--           (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))))
-- T === (λ (_x : Type (max u v)), _x)
-- t : a
-- t === (@vertical_composition_of_NaturalTransformations (C × C) C (@MonoidalStructure.tensor C m)
--           (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--           (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m)))
--           (@isomorphism.Isomorphism.morphism (FunctorCategory (C × C) C) (@MonoidalStructure.tensor C m)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--              (@braided_monoidal_category.Symmetry.braiding C m β))
--           (@whisker_on_left (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--              (@isomorphism.Isomorphism.morphism (FunctorCategory (C × C) C) (@MonoidalStructure.tensor C m)
--                 (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--                 (@braided_monoidal_category.Symmetry.braiding C m β)))) 
-- b === (@NaturalTransformation (C × C) C (@MonoidalStructure.tensor C m) (@MonoidalStructure.tensor C m))
-- e : a = b

-- @eq.rec α a T b e : T b
-- T b == b

-- f === @NaturalTransformation.components (C × C) C (@MonoidalStructure.tensor C m)
-- What sort of thing is f?
-- f : Π F : (Functor (C × C) C), S F → T F
-- for two different type families S and T.

-- Now b : S F1, while a : S F2, and e : a = b

-- (@eq.rec β c S s d f) : S d

-- but it also has to be of type T a.

-- lemma foo : { β : Type } { c : α } { S : β → Type } ( s : S c ) { d : β } ( f : c = d )
--             { α : Type } 
-- @eq.rec α a T (@eq.rec β c S s d f) b e


-- (@eq.rec (Functor (C × C) C) (@MonoidalStructure.tensor C m)
--                 (λ (a : Functor (C × C) C), a = @MonoidalStructure.tensor C m)
--                 (@eq.refl (TensorProduct C) (@MonoidalStructure.tensor C m))
--                 (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))
--                 (@eq.symm (Functor (C × C) C)
--                    (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))
--                    (@MonoidalStructure.tensor C m)
--                    (FunctorComposition.left_identity (C × C) C (@MonoidalStructure.tensor C m))))


lemma {u} bar { α : Type u } { a : α } { b : α } ( p : a = b ) : @eq.rec α a (λ b: α, b = a) (eq.refl a) b p = eq.symm p :=
begin
  cases p,
  reflexivity
end

lemma {u} foo { α : Type u } { a b : α } { p : a = b } : eq.symm (eq.symm p) = p := by reflexivity

@[simp] lemma {u v w} function_of_eq.rec { α : Type u } { a : α } { T : α → Type v } { S : α → Type w } ( t : T a ) { b : α } ( e : a = b ) ( f : Π { c : α }, T c → S c ) :
  @f b ( @eq.rec α a T t b e ) = @eq.rec α a S (@f a t) b e :=
begin
  cases e,
  reflexivity
end
@[simp] lemma {u v w} function_of_eq.drec { α : Type u } { a : α } { T : Π b : α, a = b → Type v } { S : Π b : α, a = b → Type v } ( t : T a (eq.refl a)) { b : α } ( e : a = b ) ( f : Π { c : α } { p : a = c }, T c p → S c p ) :
  f ( @eq.drec α a T t b e ) = @eq.drec α a S (f t) b e :=
begin
  cases e,
  reflexivity
end

@[simp] lemma {u v w} function_of_eq.rec' { α : Type u } { a : α } { T : α → Type v } { S : α → Type w } ( t : T a ) { b : α } ( e : a = b ) ( f : Π { c : α }, T c → S c ) :
  f ( @eq.rec α a T t b e ) = @eq.rec α a S (f t) b e :=
begin
  cases e,
  reflexivity
end


lemma {u v} symmetry_in_terms_of_natural_transformations { C : Category.{u v} } { m : MonoidalStructure C } ( β : Symmetry m ) : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor := 
  begin
    apply NaturalTransformations_componentwise_equal,
    intros,
    dsimp,
    unfold_unfoldable_hypotheses,
    induction X with X1 X2,
    unfold squared_Braiding._proof_1,
    unfold transport,
    -- rewrite bar (eq.symm (FunctorComposition.left_identity (C × C) C (m.tensor))),
    -- rewrite foo,
    rewrite function_of_eq.rec,
    -- At this point we have an unpleasant goal involving many eq.rec's, that I can't seem to do anything with.
    -- C : Category,
    -- m : MonoidalStructure C,
    -- β : braided_monoidal_category.Symmetry m,
    -- X1 X2 : C.Obj
    -- ⊢ (eq.drec
    --      (vertical_composition_of_NaturalTransformations ((β.braiding).morphism)
    --         (whisker_on_left (SwitchProductCategory C C) ((β.braiding).morphism)))
    --      (eq.rec
    --         (eq.rec (eq.rec (eq.refl (m.tensor)) (eq.symm (FunctorComposition.left_identity (C × C) C (m.tensor))))
    --            (eq.symm (switch_twice_is_the_identity C C)))
    --         (FunctorComposition.associativity (SwitchProductCategory C C) (SwitchProductCategory C C)
    --            (m.tensor)))).components
    --     (X1, X2) = (IdentityNaturalTransformation (m.tensor)).components (X1, X2)
    --
    -- Let's now type check that by hand, following Jeremy's explanation "if e : a = b, and t : T a, then eq.rec t e : T b".
    --
    -- 1) We have 
    --      eq.rec (eq.refl (m.tensor)) (eq.symm (FunctorComposition.left_identity (C × C) C (m.tensor)))
    --    Here we take T to be the type family _ = m.tensor (and this can be confirmed via `set_option pp.implicit true`),
    --    and so see that this is a proof of (writing things informally)
    --      id_(C × C) ∘ m.tensor = m.tensor
    -- 2) Next we have
    --      eq.rec (eq.rec (eq.refl (m.tensor)) (eq.symm (FunctorComposition.left_identity (C × C) C (m.tensor))))
    --            (eq.symm (switch_twice_is_the_identity C C))
    --    and again we take T to be _ = m.tensor, so we have a proof of
    --      (switch ∘ switch) ∘ m.tensor = m.tensor
    -- 3) and the next step takes us to
    --      switch ∘ (switch ∘ m.tensor) = m.tensor
    -- 4) We then have 
    --     (eq.drec
    --      (vertical_composition_of_NaturalTransformations ((β.braiding).morphism)
    --         (whisker_on_left (SwitchProductCategory C C) ((β.braiding).morphism)))
    --      (eq.rec
    --         (eq.rec (eq.rec (eq.refl (m.tensor)) (eq.symm (FunctorComposition.left_identity (C × C) C (m.tensor))))
    --            (eq.symm (switch_twice_is_the_identity C C)))
    --         (FunctorComposition.associativity (SwitchProductCategory C C) (SwitchProductCategory C C)
    --            (m.tensor))))
    --    which is a bit scary, as it involves drec instead of rec, but ignoring that we see that now we have
    --    the type family
    --       T = NaturalTransformation m.tensor _,
    --    the term
    --       t = (vertical_composition_of_NaturalTransformations ((β.braiding).morphism)
    --         (whisker_on_left (SwitchProductCategory C C) ((β.braiding).morphism)))
    --    of type T a, where
    --       a = switch ∘ (switch ∘ m.tensor)
    --    and we obtain a new term of type T b, where b = m.tensor.

    -- That all seems perfectly reasonable, but doesn't help us. We want to apply a function to this term!
    -- In particular we want to apply `λ α, NaturalTransformation.components α (X1, X2)` to our final (eq.drec t e) term.
    -- In generally, if t : T a, e : a = b, and eq.rec t e : T b, and we have some function from f : Π c, T c → S c,
    -- we can see that `f ( eq.rec t e ) : S b` should just be equal to `eq.rec (f t) e`
    -- Is this not a lemma that Lean knows already?
    admit   
  end

lemma {u v} symmetric_in_terms_of_components { C : Category.{u v} } { m : MonoidalStructure C } ( β : Braiding m ) ( e : squared_Braiding (β.braiding) = IdentityNaturalTransformation m.tensor ) : Symmetry m := {
  β with 
    symmetry := λ X Y : C.Obj, begin
                                 refine ( cast _ (congr_fun (congr_arg NaturalTransformation.components e) (X, Y)) ),
                                 unfold_unfoldable,
                                 unfold squared_Braiding._proof_1,
                                 -- Again, we're stuck with eq.rec,

                                 admit
                               end
}

end tqft.categories.braided_monoidal_category
