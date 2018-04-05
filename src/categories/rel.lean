import .category

open categories

definition Rel : category Type := {
  Hom := λ X Y, X → Y → Prop,
  identity := λ X, λ x y, x = y,
  compose := λ X Y Z f g x z, ∃ y, f x y ∧ g y z,
}