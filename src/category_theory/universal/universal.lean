-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .initial
import ..isomorphism
import ..natural_transformation
import ..graph
import ..types
import ..util.hlist

open categories
open categories.functor
open categories.isomorphism
open categories.initial
open categories.types
open categories.util

namespace categories.universal

structure Cone { J C : Category } ( F : Functor J C ) :=
  ( cone_point    : C.Obj )
  ( cone_maps     : Π j : J.Obj, C.Hom cone_point (F.onObjects j) )
  ( commutativity : Π { j k : J.Obj }, Π f : J.Hom j k, C.compose (cone_maps j) (F.onMorphisms f) = cone_maps k )

attribute [simp,ematch] Cone.commutativity

structure ConeMorphism { J C : Category } { F : Functor J C } ( X Y : Cone F ) :=
  ( morphism      : C.Hom X.cone_point Y.cone_point )
  ( commutativity : Π j : J.Obj, C.compose morphism (Y.cone_maps j) = (X.cone_maps j) )

attribute [simp,ematch] ConeMorphism.commutativity

@[pointwise] lemma ConeMorphism_componentwise_equal
  { J C : Category } { F : Functor J C } { X Y : Cone F }
  { f g : ConeMorphism X Y }
  ( w : f.morphism = g.morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

definition Cones { J C : Category } ( F : Functor J C ) : Category :=
{
  Obj            := Cone F,
  Hom            := λ X Y, ConeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ C.compose f.morphism g.morphism, ♮ ⟩,
  identity       := λ X, ⟨ C.identity X.cone_point, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

structure Cocone { J C : Category } ( F : Functor J C ) :=
  ( cocone_point  : C.Obj )
  ( cocone_maps   : Π j : J.Obj, C.Hom (F.onObjects j) cocone_point )
  ( commutativity : Π { j k : J.Obj }, Π f : J.Hom j k, C.compose (F.onMorphisms f) (cocone_maps k) = cocone_maps j )

local attribute [simp,ematch] Cocone.commutativity

structure CoconeMorphism { J C : Category } { F : Functor J C } ( X Y : Cocone F ) :=
  ( morphism      : C.Hom X.cocone_point Y.cocone_point )
  ( commutativity : Π j : J.Obj, C.compose (X.cocone_maps j) morphism = (Y.cocone_maps j) )

local attribute [simp,ematch] CoconeMorphism.commutativity

@[pointwise] lemma CoconeMorphism_componentwise_equal
  { J C : Category } { F : Functor J C } { X Y : Cocone F }
  { f g : CoconeMorphism X Y }
  ( w : f.morphism = g.morphism ) : f = g :=
  begin
    induction f,
    induction g,
    blast
  end

definition Cocones { J C : Category } ( F : Functor J C ) : Category :=
{
  Obj            := Cocone F,
  Hom            := λ X Y, CoconeMorphism X Y,
  compose        := λ X Y Z f g, ⟨ C.compose f.morphism g.morphism, ♮ ⟩,
  identity       := λ X, ⟨ C.identity X.cocone_point, ♮ ⟩,
  left_identity  := ♯,
  right_identity := ♯,
  associativity  := ♯
}

definition LimitCone   { J C : Category } ( F : Functor J C ) := TerminalObject (Cones F)
definition ColimitCone { J C : Category } ( F : Functor J C ) := InitialObject (Cocones F)

structure Equalizer { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) :=
  ( equalizer     : C.Obj )
  ( inclusion     : C.Hom equalizer X )
  ( witness       : C.compose inclusion f = C.compose inclusion g )
  ( map           : ∀ { Z : C.Obj } ( k : C.Hom Z X ) ( w : C.compose k f = C.compose k g ), C.Hom Z equalizer )
  ( factorisation : ∀ { Z : C.Obj } ( k : C.Hom Z X ) ( w : C.compose k f = C.compose k g ), C.compose (map k w) inclusion = k )
  ( uniqueness    : ∀ { Z : C.Obj } ( a b : C.Hom Z equalizer ) ( witness : C.compose a inclusion = C.compose b inclusion ), a = b )

-- Or should we write out yet another structure, and prove it agrees with the equalizer?
definition Kernel { C : Category } [ Z : ZeroObject C ] { X Y : C.Obj } ( f : C.Hom X Y ) := Equalizer f ( Z.zero_morphism X Y )

attribute [simp,ematch] Equalizer.factorisation
attribute [pointwise] Equalizer.inclusion Equalizer.map
attribute [pointwise] Equalizer.uniqueness

structure BinaryProduct { C : Category } ( X Y : C.Obj ) :=
  ( product             : C.Obj )
  ( left_projection     : C.Hom product X )
  ( right_projection    : C.Hom product Y )
  ( map                 : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.Hom Z product )
  ( left_factorisation  : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.compose (map f g) left_projection  = f ) 
  ( right_factorisation : ∀ { Z : C.Obj } ( f : C.Hom Z X ) ( g : C.Hom Z Y ), C.compose (map f g) right_projection = g ) 
  ( uniqueness          : ∀ { Z : C.Obj } ( f g : C.Hom Z product )
                            ( left_witness  : C.compose f left_projection  = C.compose g left_projection  )
                            ( right_witness : C.compose f right_projection = C.compose g right_projection ), f = g )

attribute [simp,ematch] BinaryProduct.left_factorisation BinaryProduct.right_factorisation 
attribute [pointwise] BinaryProduct.left_projection BinaryProduct.right_projection BinaryProduct.map
attribute [pointwise] BinaryProduct.uniqueness

-- PROJECT: hmm, hlist.indexed_map isn't really usable?
-- structure FiniteProduct { C : Category } ( X : list C.Obj ) :=
--   ( product       : C.Obj )
--   ( projection    : hlist (X.map (λ x, C.Hom product x) ) )
--   ( map           : ∀ { Z : C.Obj } ( f : hlist (X.map (λ x, C.Hom Z x) ) ), C.Hom Z product )
--   ( factorisation : ∀ { Z : C.Obj } ( f : hlist (X.map (λ x, C.Hom Z x) ) ), sorry )
--   ( uniqueness    : ∀ { Z : C.Obj } ( f g : C.Hom Z product ) ( witness : hlist.indexed_map (λ x p, C.compose f p = C.compose g p) X projection  ), f = g )

structure Product { C : Category } { I : Type } ( F : I → C.Obj ) :=
  ( product       : C.Obj )
  ( projection    : Π i : I, C.Hom product (F i) )
  ( map           : ∀ { Z : C.Obj } ( f : Π i : I, C.Hom Z (F i) ), C.Hom Z product )
  ( factorisation : ∀ { Z : C.Obj } ( f : Π i : I, C.Hom Z (F i) ) ( i : I ), C.compose (map f) (projection i) = f i )
  ( uniqueness    : ∀ { Z : C.Obj } ( f g : C.Hom Z product ) ( witness : ∀ i : I, C.compose f (projection i) = C.compose g (projection i)), f = g )

attribute [simp,ematch] Product.factorisation
attribute [pointwise] Product.projection Product.map
attribute [pointwise] Product.uniqueness

structure Coequalizer { C : Category } { X Y : C.Obj } ( f g : C.Hom X Y ) :=
  ( coequalizer   : C.Obj )
  ( projection    : C.Hom Y coequalizer )
  ( witness       : C.compose f projection = C.compose g projection )
  ( map           : ∀ { Z : C.Obj } ( k : C.Hom Y Z ) ( w : C.compose f k = C.compose g k ), C.Hom coequalizer Z )
  ( factorisation : ∀ { Z : C.Obj } ( k : C.Hom Y Z ) ( w : C.compose f k = C.compose g k ), C.compose projection (map k w) = k )
  ( uniqueness    : ∀ { Z : C.Obj } ( a b : C.Hom coequalizer Z ) ( witness : C.compose projection a = C.compose projection b ), a = b )

attribute [simp,ematch] Coequalizer.factorisation
attribute [pointwise] Coequalizer.projection Coequalizer.map
attribute [pointwise] Coequalizer.uniqueness

definition Cokernel { C : Category } [ Z : ZeroObject C ] { X Y : C.Obj } ( f : C.Hom X Y ) := Coequalizer f ( Z.zero_morphism X Y )

structure BinaryCoproduct { C : Category } ( X Y : C.Obj ) :=
  ( coproduct           : C.Obj )
  ( left_inclusion      : C.Hom X coproduct )
  ( right_inclusion     : C.Hom Y coproduct )
  ( map                 : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.Hom coproduct Z )
  ( left_factorisation  : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.compose left_inclusion (map f g)  = f ) 
  ( right_factorisation : ∀ { Z : C.Obj } ( f : C.Hom X Z ) ( g : C.Hom Y Z ), C.compose right_inclusion(map f g) = g ) 
  ( uniqueness          : ∀ { Z : C.Obj } ( f g : C.Hom coproduct Z )
                            ( left_witness  : C.compose left_inclusion f = C.compose left_inclusion g )
                            ( right_witness : C.compose right_inclusion f = C.compose right_inclusion g ), f = g )

attribute [simp,ematch] BinaryCoproduct.left_factorisation BinaryCoproduct.right_factorisation 
attribute [pointwise] BinaryCoproduct.left_inclusion BinaryCoproduct.right_inclusion BinaryCoproduct.map
attribute [pointwise] BinaryCoproduct.uniqueness

structure Coproduct { C : Category } { I : Type } ( X : I → C.Obj ) :=
  ( coproduct     : C.Obj )
  ( inclusion     : Π i : I, C.Hom (X i) coproduct )
  ( map           : ∀ { Z : C.Obj } ( f : Π i : I, C.Hom (X i) Z ), C.Hom coproduct Z )
  ( factorisation : ∀ { Z : C.Obj } ( f : Π i : I, C.Hom (X i) Z ) ( i : I ), C.compose (inclusion i) (map f) = f i )
  ( uniqueness    : ∀ { Z : C.Obj } ( f g : C.Hom coproduct Z ) ( witness : ∀ i : I, C.compose (inclusion i) f = C.compose (inclusion i) g), f = g )

@[reducible] definition {u} unique_up_to_isomorphism ( α : Type u ) { C : Category } ( f : α → C.Obj ) := Π X Y : α, Isomorphism C (f X) (f Y)

class Finite ( α : Type ) :=
  ( n : nat )
  ( bijection : Isomorphism CategoryOfTypes α (fin n) )

instance empty_is_Finite : Finite empty := {
  n := 0,
  bijection := begin
                 fsplit, 
                 unfold_projections, 
                 intros, 
                 induction a, 
                 unfold_projections, 
                 intros, 
                 induction a, 
                 exfalso, cases is_lt,
                 apply funext,
                 intros,
                 induction x,
                 apply funext,
                 intros,
                 induction x,
                 exfalso, cases is_lt,
              end
}

class has_InitialObject ( C : Category ) :=
  ( initial_object : InitialObject C )

class has_BinaryProducts ( C : Category ) :=
  ( binary_product : Π X Y : C.Obj, BinaryProduct X Y )
class has_FiniteProducts ( C : Category ) :=
  ( product : Π { I : Type } [ fin : Finite I ] ( f : I → C.Obj ), Product f )
class has_Products ( C : Category ) :=
  ( product : Π { I : Type } ( f : I → C.Obj ), Product f )

class has_TerminalObject ( C : Category ) :=
  ( terminal_object : TerminalObject C )

class has_BinaryCoproducts ( C : Category ) :=
  ( binary_coproduct : Π X Y : C.Obj, BinaryCoproduct X Y )
class has_FiniteCoproducts ( C : Category ) :=
  ( coproduct : Π { I : Type } [ fin : Finite I ] ( f : I → C.Obj ), Coproduct f )
class has_Coproducts ( C : Category ) :=
  ( coproduct : Π { I : Type } ( f : I → C.Obj ), Coproduct f )

class has_Equalizers ( C : Category ) :=
  ( equalizer : Π { X Y : C.Obj } ( f g : C.Hom X Y ), Equalizer f g )
class has_Coequalizers ( C : Category ) :=
  ( coequalizer : Π { X Y : C.Obj } ( f g : C.Hom X Y ), Coequalizer f g )

definition initial_object { C : Category } [ has_InitialObject C ] : C.Obj := has_InitialObject.initial_object C
definition terminal_object { C : Category } [ has_TerminalObject C ] : C.Obj := has_TerminalObject.terminal_object C

definition binary_product { C : Category } [ has_BinaryProducts C ] ( X Y : C.Obj ) := has_BinaryProducts.binary_product X Y
definition finite_product { C : Category } [ has_FiniteProducts C ] { I : Type } [ fin : Finite I ] ( f : I → C.Obj ) := @has_FiniteProducts.product C _ I fin f
definition product { C : Category } [ has_Products C ] { I : Type } ( F : I → C.Obj ) := has_Products.product F

definition binary_coproduct { C : Category } [ has_BinaryCoproducts C ] ( X Y : C.Obj ) := has_BinaryCoproducts.binary_coproduct X Y
definition finite_coproduct { C : Category } [ has_FiniteCoproducts C ] { I : Type } [ fin : Finite I ] ( f : I → C.Obj ) := @has_FiniteCoproducts.coproduct C _ I fin f
definition coproduct { C : Category } [ has_Coproducts C ] { I : Type } ( F : I → C.Obj ) := has_Coproducts.coproduct F

definition equalizer { C : Category } [ has_Equalizers C ] { X Y : C.Obj } ( f g : C.Hom X Y ) := has_Equalizers.equalizer f g
definition coequalizer { C : Category } [ has_Coequalizers C ] { X Y : C.Obj } ( f g : C.Hom X Y ) := has_Coequalizers.coequalizer f g

def {u} empty_function           { α : Sort u } : empty → α := ♯
def {u} empty_dependent_function { Z : empty → Sort u } : Π i : empty, Z i := ♯

instance FiniteProducts_give_a_TerminalObject ( C : Category ) [ has_FiniteProducts C ] : has_TerminalObject C := {
  terminal_object :=
  let empty_product := @has_FiniteProducts.product C _ empty _ empty_function in {
    terminal_object                            := empty_product.product,
    morphism_to_terminal_object_from           := λ X, empty_product.map empty_dependent_function,
    uniqueness_of_morphisms_to_terminal_object := λ X f g, empty_product.uniqueness f g empty_dependent_function
  }
}
instance FiniteProducts_from_Products ( C : Category ) [ has_Products C ] : has_FiniteProducts C := {
  product := λ _ _ f, has_Products.product f
}
instance FiniteCoproducts_give_an_InitialObject ( C : Category ) [ has_FiniteCoproducts C ] : has_InitialObject C := {
  initial_object :=
  let empty_coproduct := @has_FiniteCoproducts.coproduct C _ empty _ empty_function in {
    initial_object                              := empty_coproduct.coproduct,
    morphism_from_initial_object_to             := λ X, empty_coproduct.map empty_dependent_function,
    uniqueness_of_morphisms_from_initial_object := λ X f g, empty_coproduct.uniqueness f g empty_dependent_function
  }
}
instance FiniteCoproducts_from_Coproducts ( C : Category ) [ has_Coproducts C ] : has_FiniteCoproducts C := {
  coproduct := λ _ _ f, has_Coproducts.coproduct f
}

inductive Two : Type
| _0 : Two
| _1 : Two

open Two

local attribute [pointwise] nat.lt_succ_of_le
local attribute [simp]      nat.le_iff_lt_or_eq

instance Two_is_Finite : Finite Two := {
  n := 2,
  bijection := {
    -- FIXME why does tidy get stuck here?
    morphism := λ n, match n with
                       | _0 := ⟨ 0, begin pointwise, simp, pointwise, simp, end ⟩
                       | _1 := ⟨ 1, begin pointwise, simp end ⟩
                     end,
    inverse  := λ n, match n with
                       | ⟨ 0, _ ⟩ := _0
                       | ⟨ 1, _ ⟩ := _1 
                       | _        := _0 -- TODO we shouldn't have to do this!                   
                     end,
    witness_1 := begin
                   apply funext,
                   intros,
                   induction x, -- TODO We need to be able to specify that induction on a new type (e.g. Two) should be allowed in tidy.
                   tidy,
                 end,
    witness_2 := begin
                   apply funext,
                   intros,
                   induction x,
                   cases is_lt,
                   unfold_projections,
                   dsimp,
                   unfold Two_is_Finite._match_2, -- TODO auxiliary definitions created just a moment ago should get unfolded...
                   unfold Two_is_Finite._match_1,
                   trivial,
                   cases a,
                   unfold_projections,
                   dsimp,
                   unfold Two_is_Finite._match_2,
                   unfold Two_is_Finite._match_1,
                   trivial,
                   cases a_2
                 end
    }
  }

private definition {u} choice { α : Sort u } ( a b : α ) : Two → α 
| _0 := a
| _1 := b
private definition {v} split_choice { Z : Two → Sort v } ( f : Z _0 ) ( g : Z _1 ) : Π i : Two, Z i
| _0 := f
| _1 := g
private definition {u v} dependent_choice { α : Sort u } { Z : α → Sort v } { a b : α } ( f : Z a ) ( g : Z b ) : Π i : Two, Z (choice a b i) 
| _0 := f
| _1 := g

instance BinaryProducts_from_FiniteProducts ( C : Category ) [ has_FiniteProducts C ] : has_BinaryProducts C := {
  binary_product := λ X Y : C.Obj,
    let F := choice X Y in
    let p := finite_product F in {
      product             := p.product,
      left_projection     := p.projection _0,
      right_projection    := p.projection _1,
      map                 := λ _ f g, p.map (dependent_choice f g),
      left_factorisation  := λ _ f g, p.factorisation (dependent_choice f g) _0,
      right_factorisation := λ _ f g, p.factorisation (dependent_choice f g) _1,
      uniqueness          := λ _ f g u v, p.uniqueness f g (split_choice u v)
    }
}

-- PROJECT:
-- instance FiniteProducts_from_BinaryProducts ( C : Category ) [ has_BinaryProducts C ] : has_FiniteProducts C := {
--   product := Π { I : Type } [ fin : Finite I ] ( f : I → C.Obj ), 
-- }

end categories.universal

