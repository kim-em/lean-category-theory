import category_theory.presheaves

open category_theory
open category_theory.examples

universes u v

namespace category_theory.presheaves

/- `Presheaf` is a 2-functor CAT ⥤₂ CAT, but we're not going to prove all of that yet. -/

attribute [simp] set.preimage_id -- mathlib??

namespace Presheaf

section
variables {C : Type u} [𝒞 : category.{u v} C] {D : Type u} [𝒟 : category.{u v} D]
include 𝒞 𝒟

set_option trace.tidy true

def map (F : C ⥤ D) : Presheaf.{u v} C ⥤ Presheaf.{u v} D :=
{ obj := λ X, { X := X.X, 𝒪 := X.𝒪 ⋙ F },
  map' := λ X Y f, { f := f.f, c := whisker_on_right f.c F },
  map_id' := 
  begin 
    intros X, 
    ext1,
    swap, -- check the continuous map first (hopefully this will not be necessary after my PR)
    refl,
    ext1, -- check the equality of natural transformations componentwise
    dsimp at *, simp at *, dsimp at *,
    obviously,
  end,
  map_comp' :=
  begin
    intros X Y Z f g, 
    ext1, 
    swap,
    refl,
    tidy,
    dsimp [open_set.map_iso, nat_iso.of_components, open_set.map],
    simp,
  end }.

def map₂ {F G : C ⥤ D} (α : F ⟹ G) : (map G) ⟹ (map F) :=
{ app := λ ℱ, 
  { f := 𝟙 ℱ.X,
    c := { app := λ U, (α.app _) ≫ G.map (ℱ.𝒪.map (((open_set.map_id ℱ.X).symm U).hom)),
           naturality' := sorry }
  }, 
  naturality' := sorry }

def map₂_id {F : C ⥤ D} : map₂ (nat_trans.id F) = nat_trans.id (map F) := sorry
def map₂_vcomp {F G H : C ⥤ D} (α : F ⟹ G) (β : G ⟹ H) : map₂ β ⊟ map₂ α = map₂ (α ⊟ β) := sorry
end

section
variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞
def map_id : (map (functor.id C)) ≅ functor.id (Presheaf.{u v} C) :=  sorry
end

section
variables {C : Type u} [𝒞 : category.{u v} C] {D : Type u} [𝒟 : category.{u v} D] {E : Type u} [ℰ : category.{u v} E]
include 𝒞 𝒟 ℰ
def map_comp (F : C ⥤ D) (G : D ⥤ E) : (map F) ⋙ (map G) ≅ map (F ⋙ G) := 
{ hom := sorry,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def map₂_hcomp {F G : C ⥤ D} {H K : D ⥤ E} (α : F ⟹ G) (β : H ⟹ K) : ((map₂ α ◫ map₂ β) ⊟ (map_comp F H).hom) = ((map_comp G K).hom ⊟ (map₂ (α ◫ β))) :=
sorry
end

end Presheaf


end category_theory.presheaves