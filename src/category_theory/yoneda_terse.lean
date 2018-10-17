import category_theory.follow_your_nose

universes u₁ v₁

open category_theory

namespace terse

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

def yoneda : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁)) := ƛ X, ƛ Y : C, Y ⟶ X.

def yoneda_evaluation : (((Cᵒᵖ) ⥤ (Type v₁)) × (Cᵒᵖ)) ⥤ (Type (max u₁ v₁)) := 
(evaluation (Cᵒᵖ) (Type v₁)) ⋙ ulift_functor.{v₁ u₁}

@[simp] lemma yoneda_evaluation_map_down
  (P Q : (Cᵒᵖ ⥤ Type v₁) ×  (Cᵒᵖ)) (α : P ⟶ Q) (x : (yoneda_evaluation C) P) : 
  ((yoneda_evaluation C).map α x).down = (α.1) (Q.2) ((P.1).map (α.2) (x.down)) := rfl

def yoneda_pairing : (((Cᵒᵖ) ⥤ (Type v₁)) × (Cᵒᵖ)) ⥤ (Type (max u₁ v₁)) := 
let F := (category_theory.prod.swap ((Cᵒᵖ) ⥤ (Type v₁)) (Cᵒᵖ)) in
let G := (functor.prod ((yoneda C).op) (functor.id ((Cᵒᵖ) ⥤ (Type v₁)))) in
let H := (functor.hom ((Cᵒᵖ) ⥤ (Type v₁))) in
  (F ⋙ G ⋙ H)      

@[simp] lemma yoneda_pairing_map
  (P Q : (Cᵒᵖ ⥤ Type v₁) ×  (Cᵒᵖ)) (α : P ⟶ Q) (β : (yoneda_pairing C) (P.1, P.2)) : 
  (yoneda_pairing C).map α β = (yoneda C).map (α.snd) ≫ β ≫ α.fst := rfl

def yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C) := 
{ hom := { app := λ F x, ulift.up ((x.app F.2) (𝟙 F.2)) },
  inv := { app := λ F x, { app := λ X a, (F.1.map a) x.down } } }.

end terse