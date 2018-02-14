universes u u₁ u₂ u₃ 

class category (Obj : Type u) :=
  (Hom : Obj → Obj → Type u)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
  
section
variable {C : Type u}
variables {W X Y Z : C}
variable [category C]

def Hom : C → C → Type u := category.Hom

notation `𝟙` := category.identity
infixr ` >> `:80 := category.compose
end

structure Functor (C : Type u₁) (D : Type u₂) [category C] [category D] :=
  (onObjects   : C → D)
  (onMorphisms : Π {X Y : C},
                Hom X Y → Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C),
    onMorphisms (𝟙 X) = 𝟙 (onObjects X))
  (functoriality : ∀ {X Y Z : C} (f : Hom X Y) (g : Hom Y Z),
    onMorphisms (f >> g) = (onMorphisms f) >> (onMorphisms g))

attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality

variable {C : Type u₁}
variable {D : Type u₂}
variable [category C]
variable [category D]
instance ProductCategory : category (C × D) := {
    Hom      := (λ X Y : C × D, Hom (X.1) (Y.1) × Hom (X.2) (Y.2)),
    identity := λ X, ⟨ 𝟙 (X.1), 𝟙 (X.2) ⟩,
    compose  := λ _ _ _ f g, (f.1 >> g.1, f.2 >> g.2)
 }

instance CategoryOfTypes : category.{u+1} (Type u) := {
    Hom := λ a b, ulift.{u+1} (a → b),
    identity := λ a, ulift.up id,
    compose  := λ _ _ _ f g, ulift.up (g.down ∘ f.down)
}

inductive op (C : Type u₁) : Type u₁
| op : C → op

notation C `ᵒᵖ` := op C

def op.of : Cᵒᵖ  → C
| (op.op X) := X

instance opposite_coercion_1 : has_coe (Cᵒᵖ) C :=
  {coe := op.of}
instance opposite_coercion_2 : has_coe C (Cᵒᵖ) :=
  {coe := op.op}

instance Opposite : category (Cᵒᵖ):= {
    Hom := λ X Y : Cᵒᵖ, Hom (Y : C) (X : C),
    compose  := λ _ _ _ f g, g >> f,
    identity := λ X, 𝟙 X
}

definition HomPairing {C : Type u₁} [C_cat : category C]: Functor ((Cᵒᵖ) × C) (Type u₁) := {
  onObjects     := λ p, @Hom C _ p.1 p.2,
  onMorphisms   := λ X Y f, sorry,
  identities    := sorry,
  functoriality := sorry
}