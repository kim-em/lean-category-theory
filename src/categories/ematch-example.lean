-- class X (α : Type).
-- structure Y (α β) [X α] [X β] := (f : α → α)
-- @[ematch] theorem T (α β) [X α] [X β] (F : Y α β) (x : α) : F.f x = x := sorry
-- example (α β) [X α] [X β] (F : Y α β) (x : α) : F.f x = x :=
-- begin [smt] ematch end -- doesn't work

-- structure Y' (α /-β-/) [X α] /-[X β]-/ := (f : α → α)
-- @[ematch] theorem T' (α /-β-/) [X α] /-[X β]-/(F : Y' α /-β-/) (x : α) : F.f x = x := sorry
-- example (α /-β-/) [X α] /-[X β]-/ (F : Y' α /-β-/) (x : α) : F.f x = x :=
-- begin [smt] ematch end -- works!


universes u v u1 v1 u2 v2 u3 v3

class category (Obj : Type u) :=
  (Hom : Obj → Obj → Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f )
  (right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f )
  (associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h) )

def Hom {α : Type u} [category.{u v} α] : α → α → Type v := category.Hom

notation `𝟙` := category.identity
infixr ` ≫ `:80 := category.compose

section
variable {C : Type u1}
variables {W X Y Z : C}

@[simp] def category.left_identity_lemma [category.{u1 v1} C] (f : Hom X Y) : 𝟙 X ≫ f = f := by rw category.left_identity
@[simp] def category.right_identity_lemma [category.{u1 v1} C] (f : Hom X Y) : f ≫ 𝟙 Y = f := by rw category.right_identity
@[simp,ematch] def category.associativity_lemma [category.{u1 v1} C] (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) : (f ≫ g) ≫ h = f ≫ (g ≫ h) := by rw category.associativity
end

variable (C : Type u1)
variable (D : Type u2)
variable (E : Type u3)
variables {X Y Z : C}

structure Functor [category.{u1 v1} C] [category.{u2 v2} D] :=
  (onObjects   : C → D)
  (onMorphisms : Π {X Y : C},
                Hom X Y → Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C),
    onMorphisms (𝟙 X) = 𝟙 (onObjects X))
  (functoriality : ∀ {X Y Z : C} (f : Hom X Y) (g : Hom Y Z), onMorphisms (f ≫ g) = (onMorphisms f) ≫ (onMorphisms g))

attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality

structure Isomorphism [category.{u1 v1} C] (X Y : C) :=
(morphism : Hom X Y)
(inverse : Hom Y X)
(witness_1 : morphism ≫ inverse = 𝟙 X)
(witness_2 : inverse ≫ morphism = 𝟙 Y)
attribute [simp,ematch] Isomorphism.witness_1 Isomorphism.witness_2

-- set_option trace.debug.smt.ematch true

example
  [category.{u1 v1} C]
  [category.{u2 v2} D]
  (F : Functor C D)
  (g : Isomorphism C X Y) : (F.onMorphisms (g.morphism)) ≫ (F.onMorphisms (g.inverse)) = 𝟙 (F.onObjects X) :=
begin
 /- 
  - The goal is
  -
  - ⊢ F.onMorphisms (g.morphism) ≫ F.onMorphisms (g.inverse) = 𝟙 (F.onObjects X)
  -
  - To solve this, we need to use F.functoriality in reverse, then g.witness_1, then F.identities.
  -/
  using_smt $ smt_tactic.eblast, -- Can't work it out. :-(
  
  rw ← F.functoriality,
  rw g.witness_1,
  rw F.identities
end