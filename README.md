This repository develops the basics of category theory in Lean.

Please note that our goal is _not_ to produce a beautiful category theory library for Lean. Lean probably isn't ready for someone to try to write one!
Instead, this is an experiment to discover how plausible it is that "working mathematicians" should be interested in the current state of interactive theorem proving. As such, we're trying to set a high bar for:
* consistency with the way mathematicians think, 
* automation of everything so straightforward that a human mathematician wouldn't want to have to think about ("could an undergraduate do it?")
* concise expression (e.g. no boilerplate or excessive redundancy)

We define
* Category, functors, and natural transformations.
* The category of functors between a pair of categories.
* Isomorphisms, and equivalences of categories.

For now we only do a little of the usual development of "1-category theory", defining
* Comma, slice, and coslice categories.
* Limits ands colimits.
Notably we haven't even mentioned adjunctions!

Instead our current primary interest is developing the theory of monoidal categories. We define
* Cartesian products of categories, functors, and natural transformations.
* A monoidal category, axiomatized as a category C, along with a functor C x C \to C, and an associator natural transformation satisfying the pentagon equation, which is an isomorphism.
* A braided monoidal category, and a symmetric monoidal category.

As examples, we construct
* The symmetric monoidal category of semigroups. (Note: the current implementation is extremely slow to compile!)
* The symmetric monoidal category of types. (Note: also slow!)

Work in progress:
* The Drinfeld centre of a monoidal category.
* Internal objects (e.g. semigroups and monoids, and their modules) in monoidal categories.
* Enriched categories.


As notational conventions, we denote
* Categories by capital latin letters near the begining of the alphabet (C, D, E, and then A, B when needed),
* Objects of categories by capital latin letters near the end of the alphabet,
* Morphisms by lower case latin letters,
* Functors by capital latin letters starting at F,
* NaturalTransformations by greek letters.

