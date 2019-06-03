-- import topology.Top.presheaf
-- import category_theory.tactics.obviously

-- open category_theory
-- open category_theory.examples

-- universes u v

-- open category_theory.presheaves
-- open topological_space

-- namespace category_theory

-- /- `Presheaf` is a 2-functor CAT ⥤₂ CAT, but we're not going to prove all of that yet. -/

-- attribute [simp] set.preimage_id -- mathlib??

-- section
-- variables {C : Type u} [𝒞 : category.{u v} C] {D : Type u} [𝒟 : category.{u v} D]
-- include 𝒞 𝒟

-- set_option trace.tidy true

-- def functor.map_presheaf (F : C ⥤ D) : Presheaf.{u v} C ⥤ Presheaf.{u v} D :=
-- { obj := λ X, { X := X.X, 𝒪 := X.𝒪 ⋙ F },
--   map := λ X Y f, { f := f.f, c := whisker_right f.c F },
--   map_id' :=
--   begin
--     intros X,
--     ext1,
--     swap,
--     refl,
--     ext1, -- check the equality of natural transformations componentwise
--     dsimp at *,
--     erw functor.map_id,
--     erw functor.map_id,
--     simp,
--   end,
--   map_comp' :=
--   begin
--     intros X Y Z f g,
--     ext1,
--     swap,
--     refl,
--     tidy,
--     dsimp [opens.map_iso, nat_iso.of_components, opens.map],
--     erw functor.map_id,
--     erw functor.map_id,
--     simp,
--   end }.

-- def nat_trans.map_presheaf {F G : C ⥤ D} (α : F ⟹ G) : (G.map_presheaf) ⟹ (F.map_presheaf) :=
-- { app := λ ℱ,
--   { f := 𝟙 ℱ.X,
--     c := { app := λ U, (α.app _) ≫ G.map (ℱ.𝒪.map ((opens.map_id ℱ.X).hom.app U)),
--            naturality' := sorry }
--   },
--   naturality' := sorry }

-- lemma map₂_id {F : C ⥤ D} : (nat_trans.id F).map_presheaf = nat_trans.id (F.map_presheaf) :=
-- sorry
-- lemma map₂_vcomp {F G H : C ⥤ D} (α : F ⟹ G) (β : G ⟹ H) : β.map_presheaf ⊟ α.map_presheaf =
-- (α ⊟ β).map_presheaf := sorry
-- end

-- section
-- variables (C : Type u) [𝒞 : category.{u v} C]
-- include 𝒞
-- def presheaves.map_presheaf_id : ((functor.id C).map_presheaf) ≅ functor.id (Presheaf.{u v} C) :=
-- sorry
-- end

-- section
-- variables {C : Type u} [𝒞 : category.{u v} C]
--           {D : Type u} [𝒟 : category.{u v} D]
--           {E : Type u} [ℰ : category.{u v} E]
-- include 𝒞 𝒟 ℰ
-- def presheaves.map_presheaf_comp (F : C ⥤ D) (G : D ⥤ E) :
--   (F.map_presheaf) ⋙ (G.map_presheaf) ≅ (F ⋙ G).map_presheaf :=
-- { hom := sorry,
--   inv := sorry,
--   hom_inv_id' := sorry,
--   inv_hom_id' := sorry }

-- lemma nat_trans.map_presheaf_hcomp {F G : C ⥤ D} {H K : D ⥤ E} (α : F ⟹ G) (β : H ⟹ K) :
--   ((α.map_presheaf ◫ β.map_presheaf) ⊟ (presheaves.map_presheaf_comp F H).hom) =
--   ((presheaves.map_presheaf_comp G K).hom ⊟ ((α ◫ β).map_presheaf)) :=
-- sorry
-- end


-- end category_theory