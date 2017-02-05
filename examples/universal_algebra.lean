import data.vector

inductive {u} hlist : list (Type u) → Type (u+1)
| nil  : hlist []
| cons : Π {α : Type u} {l : list (Type u)}, α → hlist l → hlist (α::l)

notation a :: b := hlist.cons a b
notation `[` l:(foldr `, ` (h t, hlist.cons h t) hlist.nil `]`) := l

structure Operad :=
  (operations : list (ℕ × ℕ))
-- TODO relations, too!

structure algebra_over_operad (O: Operad) ( α : Type ) :=
  (operations : hlist (list.map (λ n : ℕ × ℕ, (vector α n^.fst) → (vector α n^.snd)) O^.operations)) -- heterogeneous list of functions between tuples

structure morphism_over_operad (O: Operad) { α β : Type } ( source : algebra_over_operad O α ) ( target : algebra_over_operad O β ) :=
  (map : α → β)
  (preserving_structure : hlist (list.map (λ n : ℕ × ℕ, Type /- TODO replace `Type` with the appropriate equality -/) O^.operations))