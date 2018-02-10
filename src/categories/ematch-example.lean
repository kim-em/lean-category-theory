universes u1 v1 u2 v2

structure {u v} Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f)
  (right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f)
  (associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

attribute [simp] Category.left_identity Category.right_identity
attribute [simp,ematch] Category.associativity

structure Functor (C : Category.{u1 v1}) (D : Category.{u2 v2}) :=
  (onObjects   : C.Obj → D.Obj)
  (onMorphisms : Π {X Y : C.Obj},
                C.Hom X Y → D.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C.Obj),
    onMorphisms (C.identity X) = D.identity (onObjects X))
  (functoriality : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    onMorphisms (C.compose f g) = D.compose (onMorphisms f) (onMorphisms g))


attribute [simp,ematch] Functor.identities
attribute [simp,ematch] Functor.functoriality

structure Isomorphism (C: Category) (X Y : C.Obj) :=
  (morphism : C.Hom X Y)
  (inverse : C.Hom Y X)
  (witness_1 : C.compose morphism inverse = C.identity X)
  (witness_2 : C.compose inverse morphism = C.identity Y)

attribute [simp,ematch] Isomorphism.witness_1 Isomorphism.witness_2

set_option trace.debug.smt.ematch true

example
  {C : Category.{u1 v1}}
  {D : Category.{u2 v2}} 
  {X Y : C.Obj}
  (F : Functor C D)
  (g : Isomorphism C X Y) : D.compose (F.onMorphisms (g.morphism)) (F.onMorphisms (g.inverse)) = D.identity (F.onObjects X) :=
begin
 /- 
  - The goal is
  -
  - ⊢ D.compose (F.onMorphisms (g.morphism)) (F.onMorphisms (g.inverse)) = D.identity (F.onObjects X)
  -
  - To solve this, we need to use F.functoriality in reverse, then g.witness_1, then F.identities.
  -/
  using_smt $ smt_tactic.eblast
end