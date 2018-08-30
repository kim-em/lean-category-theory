import category_theory.opposites
import category_theory.full_subcategory
import category_theory.Grothendieck_topology
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

variables {α : Type v} (X : topological_space α)

structure cover' :=
(I : Type v)
(U : I → (Open X))

-- FIXME have \func turn into ⥤?

variable {X}

def cover'.union (c : cover' X) : Open X := sorry
def cover'.union_subset (c : cover' X) (i : c.I) : c.U i ⟶ c.union := sorry

private definition inter_subset_left {C : cover' X} (i j : C.I) : (C.U i ∩ C.U j) ⊆ (C.U i) := by obviously 
private definition inter_subset_right {C : cover' X} (i j : C.I) : (C.U i ∩ C.U j) ⊆ (C.U j) := by obviously


section
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

private definition res_left
  {C : cover' X} 
  (i j : C.I) 
  (F : presheaf (Open X) D) : (F.obj (C.U i)) ⟶ (F.obj ((C.U i) ∩ (C.U j))) := 
F.map ⟨ ⟨ inter_subset_left i j ⟩ ⟩

private definition res_right
  {C : cover' X} 
  (i j : C.I) 
  (F : presheaf (Open X) D) : (F.obj (C.U j)) ⟶ (F.obj ((C.U i) ∩ (C.U j))) := 
F.map ⟨ ⟨ inter_subset_right i j ⟩ ⟩

private definition union_res
  {C : cover' X} 
  (i : C.I) 
  (F : presheaf (Open X) D) : (F.obj (C.union)) ⟶ (F.obj ((C.U i))) := 
F.map (C.union_subset i)

@[simp] lemma union_res_left_right 
  {C : cover' X} 
  (i j : C.I) 
  (F : presheaf (Open X) D) : union_res i F ≫ res_left i j F = union_res j F ≫ res_right i j F :=
sorry
end

section
variables {V : Type u} [𝒱 : category.{u v} V] [has_products.{u v} V]
include 𝒱

variables (cover : cover' X) (F : presheaf (Open X) V) 

def sections : V :=
pi.{u v} (λ c : cover.I, F.obj (cover.U c))

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

-- @[simp] lemma cover_fork_ι : (cover_fork cover F).ι = @res _ _ V _ _ cover F := rfl

variables (X V)

structure sheaf :=
(presheaf : presheaf (Open X) V)
(sheaf_condition : Π (cover : cover' X), is_equalizer (cover_fork cover presheaf))

variables {X V}

def sheaf.near (F : sheaf X V) [topological_space α] (x : α) : presheaf { U : Open X // x ∈ U } V :=
(full_subcategory_embedding (λ U : Open X, x ∈ U)).op ⋙ F.presheaf

variable [has_colimits.{u v} V]

def stalk_at (F : sheaf X V) (x : α) : V :=
colimit (F.near x)

end

-- We now provide an alternative 'pointwise' constructor for sheaves of types.

-- This should eventually be generalised to sheaves of categories with a
-- fibre functor with reflects iso and preserves limits.

structure compatible_sections (cover : cover' X) (F : presheaf (Open X) (Type u₁)) := 
  (sections      : Π i : cover.I, F.obj (cover.U i))
  (compatibility : Π i j : cover.I, res_left i j F (sections i) = res_right i j F (sections j))

structure gluing {cover : cover' X} {F : presheaf (Open X) (Type u₁)} (s : compatible_sections cover F) :=
  («section»    : F.obj cover.union)
  (restrictions : ∀ i : cover.I, (F.map (cover.union_subset i)) «section» = s.sections i)
  (uniqueness   : ∀ (Γ : F.obj cover.union) (w : ∀ i : cover.I, (F.map (cover.union_subset i)) Γ = s.sections i), Γ = «section»)

variables (X)

definition sheaf.of_types
  (presheaf        : presheaf (Open X) (Type v))
  (sheaf_condition : Π (cover : cover' X) (s : compatible_sections cover presheaf), gluing s) :
  sheaf.{v+1 v} X (Type v) :=
{ presheaf := presheaf,
  sheaf_condition := λ c,
    let sections : Π (s : fork (left c presheaf) (right c presheaf)) (x : s.X), compatible_sections c presheaf := λ s x, { sections := s.ι x, compatibility := λ i j, congr_fun (congr_fun s.w x) (i, j) } in
  { lift := λ s x, (sheaf_condition c (sections s x)).«section»,
    fac  := λ s, funext $ λ x : s.X, funext $ λ i, (sheaf_condition c (sections s x)).restrictions i,
    uniq := λ s m w, funext $ λ x : s.X, (sheaf_condition c (sections s x)).uniqueness (m x) (λ i, congr_fun (congr_fun w x) i) } }

variables {X}

instance types_has_colimits : has_colimits.{u₁+1 u₁} (Type u₁) := sorry

