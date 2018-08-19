/- Attempting to "live-formalise", from the PhD students reading group meeting on June 24 2018, starting at the beginning of homological algebra. -/

import category_theory.category
import categories.universal.instances

universes u₁ v₁ u₂ v₂

open category_theory
open category_theory.universal

class Ab_category (C: Type u₁) extends category.{u₁ v₁} C := --- we really need to setup enriched categories
  (hom_groups : Π X Y : C, comm_group (X ⟶ Y))
  (compose_is_homomorphism : Π X Y Z : C,     
    begin
    haveI : comm_group (X ⟶ Y) := by apply_instance, -- we can get these, but not the product automatically?
    haveI : comm_group ((X ⟶ Y) × (Y ⟶ Z)) := by sorry, -- surely this should just appear magically.
    exact  is_group_hom (λ p : (X ⟶ Y) × (Y ⟶ Z), p.1 ≫ p.2)
    end)


-- variables (C : Type u₁) [𝒞 : Ab_category.{u₁ v₁} C] (D : Type u₂) [𝒟 : Ab_category.{u₂ v₂} D]

-- def additive_functor extends Functor C D := sorry

class additive_category (C : Type u₁) extends (Ab_category.{u₁ v₁} C), (has_ZeroObject.{u₁ v₁} C), (has_FiniteProducts.{u₁ v₁} C)

/- Examples -/
/- Field is not additve, it doesn't have a zero object, or all products. -/
/- Abelian groups = Z-mod is an additive category. -/
/- mod-R, Vec_F, even dimensional vector spaces, are all additive categories -/

structure chain_complex (C : Type u₁) [additive_category.{u₁ v₁} C] : Type (max u₁ v₁) :=
  (chain_objects : ℤ → C)
  (differentials : Π n : ℤ, (chain_objects n) ⟶ (chain_objects (n+1)))
  -- squares to zero!

structure chain_map {C : Type u₁} [additive_category C] (M N : chain_complex C) :=
  (component : Π n : ℤ, M.chain_objects n ⟶ N.chain_objects n)
  (commutes : Π n : ℤ, component n ≫ N.differentials n = M.differentials n ≫ component (n+1))

class abelian_category (C : Type u₁) extends (additive_category.{u₁ v₁} C)/-, (has_Equalizers.{u₁ u₂} C), (has_Coequalizers.{u₁ u₂} C)-/  . 
-- TODO: monics are regular 

instance category_of_chain_complexes {C : Type u₁} [additive_category.{u₁ v₁} C] : category.{(max u₁ v₁)} (chain_complex C) :=
{ hom := λ M N, chain_map M N,
  comp := sorry,
  id := sorry,
  id_comp := sorry, comp_id := sorry, assoc := sorry
}

instance chain_complexes_are_abelian_too (C : Type u₁) [abelian_category.{u₁ v₁} C] : abelian_category (chain_complex C) := sorry
-- mostly, work componentwise


-- cycles, boundaries, homology, quasi-isomorphism
-- Example: singular chains in a topological space
