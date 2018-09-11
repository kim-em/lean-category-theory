import category_theory.sheaves
import analysis.topology.topological_structures
import category_theory.examples.categories

universes u v

open category_theory
open category_theory.examples

-- TODO redefine open_set so it is parametrised by the bundled Top?

-- Do I dare define `open_set` as a functor from Top to CAT? I don't like CAT.

def map_open_set
  {X Y : Top} (f : X ⟶ Y) : open_set Y.α ⥤ open_set X.α :=
{ obj := λ U, ⟨ f.val ⁻¹' U.s, 
    begin apply f.property, exact U.is_open, end ⟩,
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

structure TopRing :=
{β : Type u}
[Ring : comm_ring β]
[Top : topological_space β]
[TopRing : topological_ring β]

instance TopRing_comm_ring (R : TopRing) : comm_ring R.β := R.Ring
instance TopRing_topological_space (R : TopRing) : topological_space R.β := R.Top
instance TopRing_topological_ring (R : TopRing) : topological_ring R.β := R.TopRing

instance : category TopRing :=
{ hom   := λ R S, {f : R.β → S.β // is_ring_hom f ∧ continuous f },
  id    := λ R, ⟨id, by obviously⟩,
  comp  := λ R S T f g, ⟨g.val ∘ f.val, 
    begin -- TODO automate
      cases f, cases g, cases f_property, cases g_property, split, 
      dsimp, resetI, apply_instance, 
      dsimp, apply continuous.comp ; assumption  
    end⟩ }

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

structure Presheaf :=
(X : Top)
(𝒪 : presheaf (open_set X.α) C)

variables {C}

instance Presheaf_topological_space (F : Presheaf.{u v} C) : topological_space F.X.α := F.X.str 

structure Presheaf_hom (F G : Presheaf.{u v} C) :=
(f : F.X ⟶ G.X)
(c : G.𝒪 ⟹ (((map_open_set f).op) ⋙ F.𝒪))

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
  c := 
  { app := λ U, category_theory.functor.map _ (𝟙 U), 
    naturality' := 
    begin 
      intros, 
      cases X, cases Y, 
      dsimp,
      -- FIXME why can't rewrite_search take us from here?
      erw category_theory.functor.map_id,
      erw category_theory.functor.map_id,
      erw category.comp_id,
      erw category.id_comp,
      cases f, cases f,
      refl,      
    end } -- That was horrific.
}

def comp {F G H : Presheaf.{u v} C} (α : Presheaf_hom F G) (β : Presheaf_hom G H) : Presheaf_hom F H :=
{ f := α.f ≫ β.f,
  c := β.c ⊟ (whisker_on_left (map_open_set β.f).op α.c), 
}
end Presheaf_hom


instance : category (Presheaf.{u v} C) :=
{ hom := Presheaf_hom,
  id := Presheaf_hom.id,
  comp := @Presheaf_hom.comp C _,
  comp_id' := λ X Y f,
    begin 
      dsimp [Presheaf_hom.id, Presheaf_hom.comp, map_open_set, whisker_on_left, whiskering_on_left], 
      ext,
      dsimp,
      simp,
      dsimp,
      simp,
      ext,
      dsimp [functor.op],
      cases X_1,
      erw category_theory.functor.map_id,
      erw category.id_comp,
      dsimp,
      simp,
      sorry
      -- refl,
    end,
  id_comp' := λ X Y f, sorry,
    -- begin 
    --   dsimp [Presheaf_hom.id, Presheaf_hom.comp, map_open_set], 
    --   ext, 
    --   dsimp [map_open_set],
    --   simp,
    --   dsimp,
    --   cases f,
    --   dsimp,
    --   simp,
    --   ext,
    --   dsimp,
    --   erw category.comp_id,
    -- end,
  assoc' := λ W X Y Z f g h, sorry,
  -- begin
  --   ext,
  --   dsimp [Presheaf_hom.comp, map_open_set, functor.op], 
  --   simp,
  --   dsimp [Presheaf_hom.comp, map_open_set, functor.op], 
  --   cases f, cases g, cases h,
  --   dsimp,
  --   simp,
  --   funext,
  --   erw category.comp_id,
  --   erw category.comp_id,
  --   erw category.id_comp,
  -- end
}