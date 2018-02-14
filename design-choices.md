There seem to be two significant fundamental choices in the design of a category theory library for Lean. One is whether the type of objects of the category should be bundled as a field, or exposed as a parameter. The other is whether there should be two independent universe levels for objects and morphisms, or just one.

In my independent work on my category theory library, I took the first choice in each case (bundled objects, independent universes). When I made a tentative pull request of a small part of the library to `mathlib`, Mario suggested that in both cases I made the wrong choice. Since then I've been seriously exploring both options, and this document is my summary of the pros and cons. I may have made some mistakes!

--- Bundled objects vs unbundled objects ---
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
A quick aside: notice in both of these examples we don't explicitly provide evidence that the functor preserves identities or composition. This is not the sort of thing humans would put up, and an important (but only partially achieved) design goal in my library was to automate away trivial checking of definitions which would otherwise overwhelm a formal development of category theory. More on this later.

We immediately see two advantages of the unbundled approach:
1. The signatures are slightly simpler, because we refer directly to the types of objects, and use typeclass inference to provide the actual categories. Thus we write `Functor C D` instead of having to remember the additional name `FunctorCategory C D`, and can just use `×`, the built-in product of types rather than having the explicitly write `ProductCategory`.
2. It is easier to introduce notation for composition (here tentatively `>>`), because typeclass inference can automatically provide the instance of the actual category handling the composition.

