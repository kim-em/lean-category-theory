import .instances
import ..products.products
import ..discrete_category

open categories
open categories.universal
open categories.functor
open categories.products
open categories.isomorphism

local attribute [pointwise] Functors_pointwise_equal

-- These definition are *evil* --- identities between functors tend to cause horrible problems for transport later.
-- It's much better to use the natural isomorphisms defined later.
@[ematch] private lemma {u1 v1 u2 v2 u3 v3 u4 v4} FunctorComposition.associativity
  { B : Category.{u1 v1} }
  { C : Category.{u2 v2} }
  { D : Category.{u3 v3} }
  { E : Category.{u4 v4} }
  ( F : Functor B C )
  ( G : Functor C D )
  ( H : Functor D E )
   : FunctorComposition (FunctorComposition F G) H = FunctorComposition F (FunctorComposition G H) := ♮
@[simp,ematch] private lemma {u1 v1 u2 v2} FunctorComposition.left_identity
  ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) ( F : Functor C D ) : FunctorComposition (IdentityFunctor C) F = F := ♯
@[simp,ematch] private lemma {u1 v1 u2 v2} FunctorComposition.right_identity ( C : Category.{u1 v1} ) ( D : Category.{u2 v2} ) ( F : Functor C D ) : FunctorComposition F (IdentityFunctor D) = F := ♯

-- Note that this definition fixes the universe level of all the categories involved, so the witness fields are not useful as lemmas.
definition {u v} CategoryOfCategoriesAndFunctors : Category := {
  Obj := Category.{u v},
  Hom := λ C D, Functor C D,
  identity := λ C, IdentityFunctor C,
  compose  := λ _ _ _ F G, FunctorComposition F G,
  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

definition {u v} Categories_has_TerminalObject : has_TerminalObject CategoryOfCategoriesAndFunctors.{u v} :=
{
  terminal_object := {
    terminal_object                            := DiscreteCategory punit,
    morphism_to_terminal_object_from           := ♯,
    uniqueness_of_morphisms_to_terminal_object := ♯
  }
}
definition {u v} Categories_has_InitialObject : has_InitialObject CategoryOfCategoriesAndFunctors.{u v} :=
{
  initial_object := {
    initial_object                              := DiscreteCategory.{u v} (ulift empty),
    morphism_from_initial_object_to             := ♯,
    uniqueness_of_morphisms_from_initial_object := ♯
  }
}

-- definition { u v } Functor_to_ProductCategory { Z C D : Category.{u v} } ( F : Functor Z C ) ( G : Functor Z D ) : Functor Z (ProductCategory C D) :=
-- {
--   onObjects     := λ z, (F.onObjects z, G.onObjects z),
--   onMorphisms   := λ _ _ f, (F.onMorphisms f, G.onMorphisms f),
--   identities    := ♯,
--   functoriality := ♯
-- }

-- lemma {u v} congr_darg {α : Sort u} {β : α → Sort v} {a₁ a₂ : α} (f : Π a, β a) ( p : a₁ = a₂ ) : (@eq.rec α a₁ β (f a₁) a₂ p) = f a₂ :=
-- begin
--   induction p,
--   reflexivity
-- end

-- lemma transport_refl { α : Type } ( a b c : α ) ( p : b = c ) : @eq.rec α b _ (eq.refl (a, b)) c p = eq.refl (a, c) :=
-- begin
--   simp
-- end

-- @[simp] lemma transport_Prop { P Q : Prop } { a : P } { p : P = Q } : @eq.rec Prop P (λ T, T) a Q p = eq.mp p a := begin
--   reflexivity
-- end

-- lemma foo { α β : Type } ( a b : α ) ( p : a = b ) : @eq.rec α a _ (eq.refl (@prod.mk α β a)) b p = eq.refl (@prod.mk α β b) := by simp


-- definition {u v} Categories_has_FiniteProducts : has_FiniteProducts CategoryOfCategoriesAndFunctors.{u v} :=
-- {
--   Categories_has_TerminalObject with
--   binary_product := λ C D, {
--     product             := ProductCategory C D,
--     left_projection     := LeftProjection  C D,
--     right_projection    := RightProjection C D,
--     map                 := λ Z, Functor_to_ProductCategory,
--     left_factorisation  := ♯,
--     right_factorisation := ♯,
--     uniqueness          := --sorry -- PROJECT:
--                            begin
--                              intros,
--                              pointwise,
--                              {
--                                intros,
--                                apply pair_equality_4,
--                                {
--                                  pose p := congr_arg Functor.onObjects left_witness,
--                                  pose p' := congr_fun p X,
--                                  dsimp_all_hypotheses,
--                                  exact p'
--                                },
--                                {
--                                  pose p := congr_arg Functor.onObjects right_witness,
--                                  pose p' := congr_fun p X,
--                                  dsimp_all_hypotheses,
--                                  exact p'
--                                }
--                              },
--                              {
--                                intros X Y φ,
--                                apply pair_equality_4,
--                                {
--                                  pose p := congr_darg (λ T, @Functor.onMorphisms Z C T X Y φ) left_witness,
--                                  dsimp_all_hypotheses,
--                                  dunfold_everything,
--                                 --  repeat { rewrite transport_Prop },
--                                 --  rewrite foo,
--                                  exact p
--                                },
--                                admit
--                              }
--                            end
--   }
-- }
-- attribute [instance] Categories_has_FiniteProducts

-- definition {u v} Categories_has_FiniteCoproducts : has_FiniteCoproducts CategoryOfCategoriesAndFunctors.{u v} :=
-- {
--   Categories_has_InitialObject with
--   binary_coproduct := λ X Y,
--   {
--     coproduct := sum X Y,
--     left_inclusion := λ x, sum.inl x,
--     right_inclusion := λ y, sum.inr y,
--     map := λ Z f g, λ z, match z with | sum.inl x := f x | sum.inr y := g y end,
--     left_factorisation := ♯,
--     right_factorisation := ♯,
--     uniqueness := begin
--                     blast,                    
--                     induction x,
--                     exact congr_fun left_witness a,
--                     exact congr_fun right_witness a,
--                   end
--     }
--   }

-- attribute [instance] Categories_has_FiniteCoproducts