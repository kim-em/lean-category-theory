= Roadmap to an example of an affine scheme in mathlib

* Functions from a type to a (commutative) ring form a (commutative) ring.
* Continuous maps between topological spaces form a topological space.
* Continuous maps into a topological ring form a topological ring.

* Open subsets of a topological space can be thought of as topological spaces themselves.

* Now it's trivial to define the presheaf of continuous functions on a topological space.

* Products, equalizers, filtered colimits.
  * There should be a PR for these soon, in the meantime:
    * https://github.com/semorrison/lean-category-theory/blob/master/src/category_theory/universal/limits.lean
    * https://github.com/semorrison/lean-category-theory/blob/master/src/category_theory/universal/colimits.lean
    * https://github.com/semorrison/lean-category-theory/blob/master/src/category_theory/universal/limits/limits.lean

* The category of (topological) (commutative) rings has products.
  * `instance : has_products CommRing := ...`
  * For non-topological rings, most of the machinery already there, via `pi_instances`, but we'll 
    need to verify that the universal properties can be proved effortlessly.
  * Later, one wants to show that the forgetful functors to `Type u` are monadic, and hence
    create limits, and one dreams that this even gives limits which are defeq to the "by hand"
    versions.

* (Topological) (commutative) rings have filtered colimits.
  * Directed colimits is enough at first, but filtered colimits will be needed eventually when 
    someone wants sheaves on sites.
* The filtered colimit of the presheaf of continuous functions along the poset of neighbourhoods of 
  a point looks like germs at that point.

* The germ of continuous functions to `ℂ` at a point `x` is a local ring.

* The forgetful functor `CommRing ⥤ (Type u)` reflects isomorphisms.
* The forgetful functor `CommRing ⥤ (Type u)` preserves limits.
  * We can do this by hand, or better, show that it is represented by `ℤ[x]`, and hence that it
    preserves limits. (Either directly, or because more generally right adjoints preserve limits.)

* In order to verify a presheaf of rings is a sheaf, it's now enough to look at the underlying 
  presheaf of types, because one should be able to prove:
  * ````
    variables {α : Type u} [topological_space α]
	variables {V : Type (u+1)} [𝒱 : large_category V] [has_products.{u+1 u} V] (ℱ : V ⥤ (Type u)) 
	          [faithful ℱ] [preserves_limits ℱ] [reflects_isos ℱ]
	include 𝒱

	def sheaf.of_sheaf_of_types
	  (presheaf : presheaf (open_set α) V)
	  (underlying_is_sheaf : is_sheaf (presheaf ⋙ ℱ)) : is_sheaf presheaf := sorry
	````  
* On the other hand, this doesn't help for presheaves of topological rings, so:
  * Show that the presheaf of topological rings given by continuous functions to `ℂ` satisfies the
    sheaf condition.
    
* Almost trivial: write down the definition of a locally ringed space
  ````
  variables (α : Type v) [topological_space α]

  def structure_sheaf := sheaf.{v+1 v} α CommRing

  structure ringed_space :=
  (𝒪 : structure_sheaf α)

  structure locally_ringed_space extends ringed_space α :=
  (locality : ∀ x : α, is_local_ring (stalk_at.{v+1 v} 𝒪 x).1)
  ````
  and observe we've got all the ingredients to make an example out of continuous functions to `ℂ`.
  * Although consider the alternative description of locality, which doesn't require computing stalks:
    https://ncatlab.org/nlab/show/locally+ringed+topological+space#on_the_locality_condition
    How generally does this work?

* Define the category of locally_ringed_spaces, as tuples `(f, f', w)`, `f` a continuous map, `f'` a
  natural transformation `Y.𝒪 ⟹ f_* X.𝒪`, and `w` some information about preserving maximal ideals
  of stalks.

* Define `Spec R` as a `locally_ringed_space` for `R` a commutative ring, and morever `TopSpec R`
  as a `topological_locally_ringed_space` for `R` a topological commutative ring, and verify that
  the example above is isomorphic to `TopSpec (continuous_map X ℂ)`.