import category_theory.follow_your_nose

universes u₁ v₁

open category_theory

namespace terse

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

def yoneda : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁)) := ƛ X, ƛ Y : C, Y ⟶ X.

def yoneda_evaluation : ((Cᵒᵖ) × ((Cᵒᵖ) ⥤ (Type v₁))) ⥤ (Type (max u₁ v₁)) :=
(evaluation_uncurried (Cᵒᵖ) (Type v₁)) ⋙ ulift_functor.{v₁ u₁}

@[simp] lemma yoneda_evaluation_map_down
  (P Q : (Cᵒᵖ) × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (x : (yoneda_evaluation C).obj P) :
  ((yoneda_evaluation C).map α x).down = (α.2).app (Q.1) ((P.2).map (α.1) (x.down)) := rfl

def yoneda_pairing : ((Cᵒᵖ) × ((Cᵒᵖ) ⥤ (Type v₁))) ⥤ (Type (max u₁ v₁)) :=
let F := (functor.prod ((yoneda C).op) (functor.id ((Cᵒᵖ) ⥤ (Type v₁)))) in
let G := (functor.hom ((Cᵒᵖ) ⥤ (Type v₁))) in
  (F ⋙ G)

@[simp] lemma yoneda_pairing_map
  (P Q : (Cᵒᵖ) × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : (yoneda_pairing C).obj P) :
  (yoneda_pairing C).map α β = (yoneda C).map (α.1) ≫ β ≫ α.2 := rfl

def yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C) := 
{ hom := { app := λ F x, ulift.up ((x.app F.1) (𝟙 F.1)) },
  inv := { app := λ F x, { app := λ X a, (F.2.map a) x.down } } }.

end terse