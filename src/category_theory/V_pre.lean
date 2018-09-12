import category_theory.examples.topological_spaces
import category_theory.examples.categories
import category_theory.functor_category
import category_theory.functor_categories.whiskering
import category_theory.natural_isomorphism

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

@[simp] def map_open_set_id (X : Top) : map_open_set (𝟙 X) ≅ functor.id (open_set X.α) := 
{ hom :=
  { app := λ U, 𝟙 U },
  inv :=
  { app := λ U, 𝟙 U }
}

def map_open_set_iso {X Y : Top} (f g : X ⟶ Y) (h : f = g) : map_open_set f ≅ map_open_set g := 
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg _ (congr_arg _ h)) _) ) (by obviously)

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

structure Presheaf :=
(X : Top)
(𝒪 : (open_set X.α) ⥤ C)

variables {C}

instance Presheaf_topological_space (F : Presheaf.{u v} C) : topological_space F.X.α := F.X.str 

structure Presheaf_hom (F G : Presheaf.{u v} C) :=
(f : F.X ⟶ G.X)
(c : G.𝒪 ⟹ ((map_open_set f) ⋙ F.𝒪))

@[extensionality] lemma ext {F G : Presheaf.{u v} C} (α β : Presheaf_hom F G)
  (w : α.f = β.f) (h : α.c ⊟ (whisker_on_right (map_open_set_iso _ _ w).hom F.𝒪) = β.c)
  : α = β :=
begin
-- TODO refactor
  cases α, cases β,
  dsimp at w,
  subst w,
  congr,
  ext,
  have h' := congr_fun (congr_arg nat_trans.app h) X,
  clear h,
  dsimp at h',
  dsimp [map_open_set_iso,whisker_on_right,whiskering_on_right,nat_iso.of_components,nat_trans.hcomp] at h',
  simp at h',
  rw ← h', -- Ugh, we could directly simplify h' to match the goal.
  obviously,
end

namespace Presheaf_hom
def id (F : Presheaf.{u v} C) : Presheaf_hom F F :=
{ f := 𝟙 F.X,
  -- TODO write this as a calc block for readability.
  c := ((functor.id_comp _).inv) ⊟ (whisker_on_right (map_open_set_id _).inv _),
}

def comp {F G H : Presheaf.{u v} C} (α : Presheaf_hom F G) (β : Presheaf_hom G H) : Presheaf_hom F H :=
{ f := α.f ≫ β.f,
  c := β.c ⊟ (whisker_on_left (map_open_set β.f) α.c), -- It's hard to believe this typechecks!
}
end Presheaf_hom

instance : category (Presheaf.{u v} C) :=
{ hom := Presheaf_hom,
  id := Presheaf_hom.id,
  comp := @Presheaf_hom.comp C _,
  comp_id' := λ X Y f,
    begin 
      ext1,
      -- Check the comorphisms
      ext1, -- compare natural transformations componentwise
      dsimp [Presheaf_hom.id, Presheaf_hom.comp], 
      dsimp [whisker_on_right, whiskering_on_right, whisker_on_left, whiskering_on_left],
      simp,
      erw [category_theory.functor.map_id],
      simp,
      cases X_1, -- Why do we need to do cases before we can finish??!
      simp,
      refl,
      -- Check the functions
      dsimp [Presheaf_hom.id, Presheaf_hom.comp], 
      simp,
    end,
  id_comp' := λ X Y f, --sorry,
  begin 
      ext1,
      -- Check the comorphisms
      ext1, -- compare natural transformations componentwise
      dsimp [Presheaf_hom.id, Presheaf_hom.comp], 
      dsimp [whisker_on_right, whiskering_on_right, whisker_on_left, whiskering_on_left],
      simp,
      erw [category_theory.functor.map_id, category.comp_id, category.comp_id],
      -- Check the functions
      dsimp [Presheaf_hom.id, Presheaf_hom.comp], 
      simp,
    end,
  assoc' := λ W X Y Z f g h, --sorry,
  begin
    ext1,
    swap,
    -- Check the functions
    { dsimp [Presheaf_hom.comp], 
      simp, },
    -- Check the comorphisms
    { dsimp [Presheaf_hom.comp], 
      simp,
      refl, },
  end
}