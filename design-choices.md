There seem to be two significant fundamental choices in the design of a category theory library for Lean. One is whether the type of objects of the category should be bundled as a field, or exposed as a parameter. The other is whether there should be two independent universe levels for objects and morphisms, or just one.

In my independent work on my category theory library, I took the first choice in each case (bundled objects, independent universes). When I made a tentative pull request of a small part of the library to `mathlib`, Mario suggested that in both cases I made the wrong choice. Since then I've been seriously exploring both options, and this document is my summary of the pros and cons. I may have made some mistakes!

# Bundled objects vs unbundled objects
Here's the 'bundled' version of `Category`:
````
structure {u v} Category :=
(Obj : Type u)
(Hom : Obj → Obj → Type v)
(identity : Π X : Obj, Hom X X)
(compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
(left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f . obviously) -- we supply the `obviously` here as the default tactic for filling in this field
(right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f . obviously)
(associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), compose (compose f g) h = compose f (compose g h) . obviously)
````

and here's the 'unbundled' version, called `category`:
````
class category (Obj : Type u) :=
(Hom : Obj → Obj → Type u)
(identity : Π X : Obj, Hom X X)
(compose  : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
(left_identity  : ∀ {X Y : Obj} (f : Hom X Y), compose (identity X) f = f . obviously)
(right_identity : ∀ {X Y : Obj} (f : Hom X Y), compose f (identity Y) = f . obviously)
(associativity  : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), compose (compose f g) h = compose f (compose g h) . obviously)
````

As a quick example of how things look later as a consequence of the two choices, we might have
````
definition Evaluation : Functor (ProductCategory (FunctorCategory C D) C) D := {
  onObjects     := λ p, p.1.onObjects p.2,
  onMorphisms   := λ x y f, D.compose (x.1.onMorphisms f.2) (f.1.components y.2)
}
````
or
````
definition Evaluation : Functor ((Functor C D) × C) D := {
  onObjects     := λ p, p.1.onObjects p.2,
  onMorphisms   := λ x y f, (x.1.onMorphisms f.2) >> (f.1.components y.2)
}
````
A quick aside: notice in both of these examples we don't explicitly provide evidence that the functor preserves identities or composition. This is not the sort of thing humans would put up, and an important (but only partially achieved) design goal in my library was to automate away trivial checking of definitions which would otherwise overwhelm a formal development of category theory. In both case the evidence is provided by a tactic. More on this later.

We immediately see two advantages of the unbundled approach:
1. The signatures are slightly simpler, because we refer directly to the types of objects, and use typeclass inference to provide the actual categories. Thus we write `Functor C D` instead of having to remember the additional name `FunctorCategory C D`, and can just use `×`, the built-in product of types rather than having the explicitly write `ProductCategory`.
2. It is easier to introduce notation for composition (here tentatively `>>`), because typeclass inference can automatically provide the instance of the actual category handling the composition.

However, not having to specify the category quickly becomes a mixed blessing --- because in the cases where we _need_ to specify the category, it is rather cumbersome to do so (lots of `@`s and `_`s), or worse.

A historical note: there have been many previous category theory libraries in interactive theorem provers. Let me mention two:
1. The development in Lean 2, at https://github.com/leanprover/lean2/tree/master/library/algebra/category. This uses unbundled objects, but not typeclasses. I think that development stopped just short of running into the problem described below.
2. "Experience Implementing a Performant Category-Theory Library in Coq", by Gross, Chlipala, Spivak, https://arxiv.org/pdf/1401.7694.pdf. They decide to use fully bundled categories, and explain in detail why. 
Two quotes: 'Switching from the version where the types
of objects and morphisms were parameters brought a factor of three speed-up
in compilation time over our whole development.' and 'One of the main benefits to making all of
the relevant components arguments, ..., is that it allows the use of type-class resolution without having to
worry about overlapping instances.'

## Same objects, many categories
Unlike in the situation with undergraduate abstract algebra (rings and fields and so on), where we typically only think about a single ring structure on a given set at a time, in applications of category theory the objects very often do not specify the category. In all the first examples there is an obvious natural category structure (the category of rings, or modules for an algebra, etc), and so it seems very nice to just be able to refer to the objects and write things like `Functor Rings Types`. One of the first places that we want to consider two different category structures on the same collection of objects is in defining opposite categories. I'll use this example to illustrate the difficulties below. I also want to emphasise that this rather formal example is just one of many. Others include:

1. Localising a category at a set of morphisms, by keeping the same objects, but defining morphisms as certain zig-zags modulo relations.
2. Defining the derived category. (This is a special case of 1: we take the category of chain complexes and chain maps between them, and then form a new category that still has chain complexes as objects, but we formally invert all the quasi-isomorphisms, those inducing isomorphisms on homology.)
3. Defining projective modules for an algebra `A` in a monoidal category `C`, by first defining the category of free modules, which has the same objects as `C`, but the morphisms from `X` to `Y` are the morphisms in `C` from `X` to `Y (x) A`. We then get the category of projective modules by idempotent completing.

In the bundled approach to a category theory library, all this is no problem. We just refer to the different categories explicitly.

If anyone has suggestions for how to handle this in the unbundled approach, I'm happy to hear. Let me demonstrate how the 'obvious solution' is not ideal. Let's try to define the opposite category. We're going to need a little wrapper object which we can use to distinguish "objects in C" and "objects in C thought of as objects in C^op".
````
universes u₁

inductive op (C : Type u₁) : Type u₁
| op : C → op

notation C `ᵒᵖ` := op C

variable {C : Type u₁}
variable [category C]

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
````
So far, this looks great.

However, as is always the case with these situations where we have two different categories with the same underlying objects, we need to talk about both at the same time. A good example here is the pairing functor, `Functor (C × (Cᵒᵖ)) (Type u₁)`, which sends a pair of objects `(X, Y)` to `Hom X Y`. Here's the easy construction back in the bundled world:
````
definition Opposite (C : Category) : Category := {
    Obj := C.Obj,
    Hom := λ X Y, C.Hom Y X,
    compose  := λ _ _ _ f g, C.compose g f,
    identity := λ X, C.identity X
}

definition {u v} HomPairing (C : Category.{u v}) : Functor ((Opposite C) × C) CategoryOfTypes.{v} := {
  onObjects     := λ p, C.Hom p.1 p.2,
  onMorphisms   := λ _ _ f, λ g, C.compose (C.compose f.1 g) f.2
}
````

Unfortunately, I just can't get this to work in the unbundled world:
````
definition HomPairing {C : Type u₁} [C_cat : category C]: Functor ((Cᵒᵖ) × C) (Type u₁) := {
  onObjects     := λ p, @Hom C _ p.1 p.2,
  onMorphisms   := λ X Y f, sorry
}
````
So far I haven't found a way to fill in `sorry`, let alone one that doesn't have a million `@`s and coercions. (Help wanted!) (An aside: I note that the category theory development in Lean also seems to have stopped at this point: https://github.com/leanprover/lean2/blob/master/library/algebra/category/adjoint.lean. They use unbundled categories, but without typeclasses.)

If anyone is interested you can play with either of these examples in the repository at https://github.com/semorrison/lean-category-theory.git. The `master` branch contains the bundled development, the `unbundled` branch contains the unbundled development (note most files in this branch don't compile). The stuff on opposites is in `src/categories/opposities.lean`.

There's also a self-contained copy of just enough of the unbundled development at https://raw.githubusercontent.com/semorrison/lean-category-theory/unbundled/src/categories/unbundled-opposites.lean if anyone wants to show me how to define the pairing.

## `ematch` struggles with typeclasses
Finally, there's another problem with the unbundled approach --- `ematch` is much less successful at discharging 'easy' goals, where you just need to rewrite a few times using associativity, functoriality, and/or naturality. It seems to choke when there are too many instances around. Thanks Mario for the following example:
````
class X (α : Type).
structure Y (α β) [X α] [X β] := (f : α → α)
@[ematch] theorem T (α β) [X α] [X β] (F : Y α β) (x : α) : F.f x = x := sorry
example (α β) [X α] [X β] (F : Y α β) (x : α) : F.f x = x :=
begin [smt] ematch end -- doesn't work

structure Y' (α /-β-/) [X α] /-[X β]-/ := (f : α → α)
@[ematch] theorem T' (α /-β-/) [X α] /-[X β]-/(F : Y' α /-β-/) (x : α) : F.f x = x := sorry
example (α /-β-/) [X α] /-[X β]-/ (F : Y' α /-β-/) (x : α) : F.f x = x :=
begin [smt] ematch end -- works!
````
I have a work-around for this (essentially replacing `ematch` with my own tool for searching for viable strings of rewrites, judging progress by calculating string edit distance between the left and right sides of an equation), but it involves introducing a whole new automation tool that may not be welcome in mathlib.

# one universe or two?
This is less of a show-stopper, but the main difficulty I ran into switching to having categories parametrised by a single universe level was that it becomes cumbersome to define the category of types. As we want `Obj := Type u`, and `Hom := λ X Y, X → Y`, we end up with `Obj : Type (u+1)` while `Hom : ... → Type u`, and thus have to put in extra `ulifts` in the definition of `Hom`. This is viable, but it's really cumbersome compared to how the category of types behaves when we allow different universe levels.

I haven't yet tried ripping out the second universe level all the way through to defining limits and colimits, but this is where I'm worried we'll run into trouble. I've found that you really want to be able to say things like "the category C, in universe levels u and v, has limits indexed by categories in universe levels w and z", and I'm not certain whether it's safe to collapse u and v, and w and z, in all applications.