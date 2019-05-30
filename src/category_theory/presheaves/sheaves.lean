import category_theory.opposites
import category_theory.full_subcategory
import category_theory.limits.types
import topology.Top.basic
import category_theory.limits.obviously


open category_theory
open category_theory.limits
open category_theory.examples
open topological_space

universes u v u₁ v₁ u₂ v₂

variable (X : Top.{v})

local attribute [back] topological_space.is_open_inter
-- local attribute [back] opens.property

instance has_inter_open_set : has_inter (opens X) :=
{ inter := λ U V, ⟨ U.val ∩ V.val, by obviously ⟩ }

instance has_inter_open_set_op : has_inter ((opens X)ᵒᵖ) := has_inter_open_set X

-- def cover_intersections_index (I : Type v) : grothendieck_category (ParallelPair_functor (@prod.fst I I) (@prod.snd I I))
-- def cover_intersections (c : cover X) : (cover_intersections_index c.I) ⥤ open_set X :=
-- { obj := λ p, match p.1 with
--   | _1 := c.U p.2.1 ∩ c.U p.2.2
--   | _2 := c.U p.2
--   end,
--   map := λ p q f, sorry
-- }

-- @[tidy] meta def sbe := `[solve_by_elim [sum.inl, sum.inr, ulift.up, plift.up, trivial] {max_rep := 5}]

-- instance (I : Type v) : category (I × I ⊕ I) :=
-- { hom := λ X Y, match (X, Y) with
--   | (sum.inl (i, j), sum.inr k) := ulift (plift (i = k)) ⊕ ulift (plift (j = k))
--   | (sum.inl (i, j), sum.inl (i', j')) := ulift (plift (i = i' ∧ j = j'))
--   | (sum.inr k, sum.inr k') := ulift (plift (k = k'))
--   | (sum.inr k, sum.inl (i, j)) := pempty
--   end,
--   id := by tidy,
--   comp := by tidy,
-- }

structure cover :=
(I : Type v)
(U : I → (opens X))

variables {X}

def cover.union (c : cover X) : opens X :=
⟨ set.Union (λ i : c.I, (c.U i).1),
  begin
  apply topological_space.is_open_sUnion,
  tidy,
  subst H_h,
  exact (c.U H_w).2
  end ⟩

def cover.sub (c : cover X) (i : c.I) : c.U i ⟶ c.union := sorry

definition cover.left (c : cover X) (i j : c.I) : (c.U i ∩ c.U j) ⟶ (c.U i) := by obviously
definition cover.right (c : cover X) (i j : c.I) : (c.U i ∩ c.U j) ⟶ (c.U j) := by obviously

section
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
variables {c : cover X} (i j : c.I) (F : (opens X)ᵒᵖ ⥤ D)
include 𝒟

definition res_left : (F.obj (c.U i)) ⟶ (F.obj ((c.U i) ∩ (c.U j))) :=
F.map (c.left i j)

definition res_right :=
F.map (c.right i j)

definition res_union : (F.obj (c.union)) ⟶ (F.obj ((c.U i))) :=
F.map (c.sub i)

@[simp] lemma res_left_right : res_union i F ≫ res_left i j F = res_union j F ≫ res_right i j F :=
begin
  dsimp [res_union, res_left, res_right],
  rw ← functor.map_comp,
  rw ← functor.map_comp,
  refl,
end
end

section
variables {V : Type u} [𝒱 : category.{u v} V] [has_products.{u v} V]
include 𝒱

variables (c : cover X) (F : (opens X)ᵒᵖ ⥤ V)

def sections : V :=
limits.pi.{u v} (λ i : c.I, F.obj (c.U i))

def overlaps : V :=
limits.pi.{u v} (λ p : c.I × c.I, F.obj (c.U p.1 ∩ c.U p.2))

def left : (sections c F) ⟶ (overlaps c F) :=
pi.pre _ (λ p : c.I × c.I, p.1) ≫ pi.map (λ p, res_left p.1 p.2 F)

def right : (sections c F) ⟶ (overlaps c F) :=
pi.pre _ (λ p : c.I × c.I, p.2) ≫ pi.map (λ p, res_right p.1 p.2 F)

def res : F.obj (c.union) ⟶ (sections c F) :=
pi.lift (λ i, res_union i F)

@[simp] lemma res_left_right' : res c F ≫ left c F = res c F ≫ right c F :=
begin
  dsimp [left, right, res],
  rw ← category.assoc,
  simp,
  rw ← category.assoc,
  simp,
end

def cover_fork : fork (left c F) (right c F) :=
fork.of_ι (res c F) (by tidy)

class is_sheaf (presheaf : (opens X)ᵒᵖ ⥤ V) :=
(sheaf_condition : Π (c : cover X), is_equalizer (cover_fork c presheaf))

variables (X V)

structure sheaf  :=
(presheaf : (opens X)ᵒᵖ ⥤ V)
(sheaf_condition : is_sheaf presheaf)

end
