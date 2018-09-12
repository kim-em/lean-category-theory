import category_theory.examples.topological_spaces
import category_theory.examples.categories
import category_theory.functor_category
import category_theory.functor_categories.whiskering

universes u v u₂ v₂

open category_theory
open category_theory.examples

-- TODO redefine open_set so it is parametrised by the bundled Top?

-- Do I dare define `open_set` as a functor from Top to CAT? I don't like CAT.

def map_open_set
  {X Y : Top} (f : X ⟶ Y) : open_set Y.α ⥤ open_set X.α :=
{ obj := λ U, ⟨ f.val ⁻¹' U.s, f.property _ U.is_open ⟩,
  map' := λ U V i, 
    begin 
      dsimp at i, 
      split, 
      split, 
      tactic.intros1, 
      dsimp at a_1, 
      dsimp,
      have p := i.down.down,
      dsimp [(≤), preorder.le, (⊆), set.subset] at p,
      apply p,
      assumption
    end }.

-- These next two are desperate attempts to solve problems below.
-- @[simp] def map_open_set_id_obj (X : Top) (U : open_set X.α) : map_open_set (𝟙 X) U = U :=
-- begin dsimp [map_open_set], cases U, congr, end
@[simp] def map_open_set_id (X : Top) : map_open_set (𝟙 X) ≅ functor.id (open_set X.α) := 
{ hom :=
  { app := λ U, 𝟙 U },
  inv :=
  { app := λ U, 𝟙 U }
}

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

section
variables (D : Type u₂) [𝒟 : category.{u₂ v₂} D]
include 𝒟 
variables (F : C ⥤ D)
@[simp] def functor.id_comp : functor.id C ⋙ F ≅ F := 
{ hom :=
  { app := λ X, 𝟙 (F X) },
  inv :=
  { app := λ X, 𝟙 (F X) }
}
end

structure Presheaf :=
(X : Top)
(𝒪 : (open_set X.α) ⥤ C)

variables {C}

instance Presheaf_topological_space (F : Presheaf.{u v} C) : topological_space F.X.α := F.X.str 

structure Presheaf_hom (F G : Presheaf.{u v} C) :=
(f : F.X ⟶ G.X)
(c : G.𝒪 ⟹ ((map_open_set f) ⋙ F.𝒪))

@[extensionality] lemma ext {F G : Presheaf.{u v} C} (α β : Presheaf_hom F G)
  (w : α.f = β.f) (h : α.c == β.c)
  : α = β :=
begin
  cases α, cases β,
  dsimp at w,
  subst w,
  congr,
  dsimp at h,
  exact eq_of_heq h,
end

namespace Presheaf_hom
def id (F : Presheaf.{u v} C) : Presheaf_hom F F :=
{ f := 𝟙 F.X,
  c := begin apply nat_trans.vcomp, swap, apply whisker_on_right (map_open_set_id _).inv, apply (functor.id_comp _ _ _).inv end
}

def comp {F G H : Presheaf.{u v} C} (α : Presheaf_hom F G) (β : Presheaf_hom G H) : Presheaf_hom F H :=
{ f := α.f ≫ β.f,
  c := β.c ⊟ (whisker_on_left (map_open_set β.f) α.c), -- It's hard to believe this typechecks!
}
end Presheaf_hom

-- set_option pp.implicit true
instance : category (Presheaf.{u v} C) :=
{ hom := Presheaf_hom,
  id := Presheaf_hom.id,
  comp := @Presheaf_hom.comp C _,
  comp_id' := λ X Y f, --sorry,
    begin 
      ext,
      -- we check the functions first
      dsimp [Presheaf_hom.id, Presheaf_hom.comp], 
      simp,
      -- and now the comorphisms
      dsimp [Presheaf_hom.id, Presheaf_hom.comp], 
      simp,
      ext, -- compare natural transformations componentwise?
      dsimp [whisker_on_right, whiskering_on_right, whisker_on_left, whiskering_on_left],
      dsimp [map_open_set],
      simp,
      erw [category_theory.functor.map_id],
      simp,
      cases X_1,
      simp,
      refl,
    end,
  id_comp' := λ X Y f, sorry,
  assoc' := λ W X Y Z f g h, --sorry
  begin
    ext,
    -- we check the functions first
    { dsimp [Presheaf_hom.comp], 
      simp, },
    -- and now the comorphisms
    dsimp [Presheaf_hom.comp], 
    simp,
    refl,
  end
}