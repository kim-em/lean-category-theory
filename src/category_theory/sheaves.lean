import category_theory.opposites
import category_theory.full_subcategory
import category_theory.universal.types
import category_theory.examples.topological_spaces

open category_theory
open category_theory.universal
open category_theory.examples.topological_spaces

universes u v u₁ v₁ u₂ v₂

section
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C] (V : Type u₂) [𝒱 : category.{u₂ v₂} V]
include 𝒞 𝒱

def presheaf := (Cᵒᵖ) ↝ V

def presheaves : category (presheaf C V) := begin unfold presheaf, apply_instance end
end

variables (α : Type v) [topological_space α]

local attribute [back] topological_space.is_open_inter
local attribute [back] open_set.is_open

instance : has_inter (open_set α) := 
{ inter := λ U V, ⟨ U.s ∩ V.s, by obviously ⟩ }

instance has_inter_op : has_inter ((open_set α)ᵒᵖ) := 
{ inter := λ U V, ⟨ U.s ∩ V.s, by obviously ⟩ }

structure cover' :=
(I : Type v)
(U : I → (open_set α))


-- FIXME have \func turn into ⥤?
variables {α}

-- TODO cleanup
def cover'.union (c : cover' α) : open_set α := ⟨ set.Union (λ i : c.I, (c.U i).1), 
  begin 
  apply topological_space.is_open_sUnion, 
  tidy, 
  subst H_h,
  exact (c.U H_w).2
  end ⟩
def cover'.union_subset (c : cover' α) (i : c.I) : c.U i ⟶ c.union := by obviously

private definition inter_subset_left {C : cover' α} (i j : C.I) : (C.U i ∩ C.U j) ⟶ (C.U i) := by obviously
private definition inter_subset_right {C : cover' α} (i j : C.I) : (C.U i ∩ C.U j) ⟶ (C.U j) := by obviously


section
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

definition res_left
  {C : cover' α} 
  (i j : C.I) 
  (F : presheaf (open_set α) D) : (F.obj (C.U i)) ⟶ (F.obj ((C.U i) ∩ (C.U j))) := 
F.map (inter_subset_left i j)

definition res_right
  {C : cover' α} 
  (i j : C.I) 
  (F : presheaf (open_set α) D) : (F.obj (C.U j)) ⟶ (F.obj ((C.U i) ∩ (C.U j))) := 
F.map (inter_subset_right i j)

private definition union_res
  {C : cover' α} 
  (i : C.I) 
  (F : presheaf (open_set α) D) : (F.obj (C.union)) ⟶ (F.obj ((C.U i))) := 
F.map (C.union_subset i)

@[simp] lemma union_res_left_right 
  {C : cover' α} 
  (i j : C.I) 
  (F : presheaf (open_set α) D) : union_res i F ≫ res_left i j F = union_res j F ≫ res_right i j F :=
begin
  dsimp [union_res, res_left, res_right],
  rw ← functor.map_comp,
  rw ← functor.map_comp,
  refl,
end
end

section
variables {V : Type u} [𝒱 : category.{u v} V] [has_products.{u v} V]
include 𝒱

variables (cover : cover' α) (F : presheaf (open_set α) V) 

def sections : V :=
pi.{u v} (λ c : cover.I, F.obj (cover.U c))

def select_section (i : cover.I) := pi.π (λ c : cover.I, F.obj (cover.U c)) i

def overlaps : V :=
pi.{u v} (λ p : cover.I × cover.I, F.obj (cover.U p.1 ∩ cover.U p.2))

def left : (sections cover F) ⟶ (overlaps cover F) := 
pi.map (λ p, p.1) (λ p, res_left p.1 p.2 F)

def right : (sections cover F) ⟶ (overlaps cover F) := 
pi.map (λ p, p.2) (λ p, res_right p.1 p.2 F)

def res : F.obj (cover.union) ⟶ (sections cover F) :=
pi.of_components (λ i, union_res i F)

@[simp] lemma res_left_right : res cover F ≫ left cover F = res cover F ≫ right cover F :=
begin
  dsimp [left, right, res],
  simp,
end

def cover_fork : fork (left cover F) (right cover F) :=
{ X := F.obj (cover.union),
  ι := res cover F, }


class is_sheaf (presheaf : presheaf (open_set α) V) :=
(sheaf_condition : Π (cover : cover' α), is_equalizer (cover_fork cover presheaf))

variables (α V)

structure sheaf  :=
(presheaf : presheaf (open_set α) V)
(sheaf_condition : is_sheaf presheaf)

variables {α V}

def sheaf.near (F : sheaf α V) (x : α) : presheaf { U : open_set α // x ∈ U } V :=
(full_subcategory_embedding (λ U : open_set α, x ∈ U)).op ⋙ F.presheaf

variable [has_colimits.{u v} V]

def stalk_at (F : sheaf α V) (x : α) : V :=
colimit (F.near x)

end
