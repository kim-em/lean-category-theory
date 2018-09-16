import category_theory.opposites
import category_theory.full_subcategory
import category_theory.universal.types
import category_theory.examples.topological_spaces

open category_theory
open category_theory.limits
open category_theory.examples

universes u v u₁ v₁ u₂ v₂

-- section
-- variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C] (V : Type u₂) [𝒱 : category.{u₂ v₂} V]
-- include 𝒞 𝒱

-- def presheaf := C ⥤ V -- I know there's usually an op on C here, but I'm having trouble with opposites, so
--                        -- you'll have to provide it yourself!

-- def presheaves : category (presheaf C V) := begin unfold presheaf, apply_instance end
-- end


variable (X : Top.{v})

local attribute [back] topological_space.is_open_inter
local attribute [back] open_set.is_open

instance : has_inter (open_set X) := 
{ inter := λ U V, ⟨ U.s ∩ V.s, by obviously ⟩ }

instance has_inter_op : has_inter ((open_set X)ᵒᵖ) := 
{ inter := λ U V, ⟨ U.s ∩ V.s, by obviously ⟩ }

structure cover' :=
(I : Type v)
(U : I → (open_set X))

variables {X}

-- TODO cleanup
def cover'.union (c : cover' X) : open_set X := ⟨ set.Union (λ i : c.I, (c.U i).1), 
  begin 
  apply topological_space.is_open_sUnion, 
  tidy, 
  subst H_h,
  exact (c.U H_w).2
  end ⟩
def cover'.union_subset (c : cover' X) (i : c.I) : c.union ⟶ c.U i := by obviously

private definition inter_subset_left {C : cover' X} (i j : C.I) : (C.U i) ⟶ (C.U i ∩ C.U j) := by obviously
private definition inter_subset_right {C : cover' X} (i j : C.I) : (C.U j) ⟶ (C.U i ∩ C.U j) := by obviously


section
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

definition res_left
  {C : cover' X} 
  (i j : C.I) 
  (F : (open_set X) ⥤ D) : (F.obj (C.U i)) ⟶ (F.obj ((C.U i) ∩ (C.U j))) := 
F.map (inter_subset_left i j)

definition res_right
  {C : cover' X} 
  (i j : C.I) 
  (F : (open_set X) ⥤ D) : (F.obj (C.U j)) ⟶ (F.obj ((C.U i) ∩ (C.U j))) := 
F.map (inter_subset_right i j)

private definition union_res
  {C : cover' X} 
  (i : C.I) 
  (F : (open_set X) ⥤ D) : (F.obj (C.union)) ⟶ (F.obj ((C.U i))) := 
F.map (C.union_subset i)

@[simp] lemma union_res_left_right 
  {C : cover' X} 
  (i j : C.I) 
  (F : (open_set X) ⥤ D) : union_res i F ≫ res_left i j F = union_res j F ≫ res_right i j F :=
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

variables (cover : cover' X) (F : (open_set X) ⥤ V) 

def sections : V :=
pi.{u v} (λ c : cover.I, F.obj (cover.U c))

def select_section (i : cover.I) := pi.π (λ c : cover.I, F.obj (cover.U c)) i

def overlaps : V :=
pi.{u v} (λ p : cover.I × cover.I, F.obj (cover.U p.1 ∩ cover.U p.2))

def left : (sections cover F) ⟶ (overlaps cover F) := 
pi.pre _ (λ p : cover.I × cover.I, p.1) ≫ pi.map (λ p, res_left p.1 p.2 F)

def right : (sections cover F) ⟶ (overlaps cover F) := 
pi.pre _ (λ p : cover.I × cover.I, p.2) ≫ pi.map (λ p, res_right p.1 p.2 F)

def res : F.obj (cover.union) ⟶ (sections cover F) :=
pi.lift (λ i, union_res i F)

@[simp] lemma res_left_right : res cover F ≫ left cover F = res cover F ≫ right cover F :=
begin
  dsimp [left, right, res],
  rw ← category.assoc,
  simp,
  rw ← category.assoc,
  simp,
end

def cover_fork : fork (left cover F) (right cover F) :=
{ X := F.obj (cover.union),
  ι := res cover F, }


class is_sheaf (presheaf : (open_set X) ⥤ V) :=
(sheaf_condition : Π (cover : cover' X), is_equalizer (cover_fork cover presheaf))

variables (X V)

structure sheaf  :=
(presheaf : (open_set X) ⥤ V)
(sheaf_condition : is_sheaf presheaf)

end
