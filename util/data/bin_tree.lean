import .nonempty_list

open tqft.util.data.nonempty_list

namespace tqft.util.data.bin_tree

universes u v

inductive bin_tree (α : Type u)
| leaf : α → bin_tree
| branch : bin_tree → bin_tree → bin_tree

namespace bin_tree

variables {α : Type u} {β : Type v}

def map (f : α → β) : bin_tree α → bin_tree β
| (leaf x) := leaf (f x)
| (branch l r) := branch (map l) (map r)

def to_list : bin_tree α → nonempty_list α
| (leaf x) := nonempty_list.singleton x
| (branch l r) := to_list l ++  to_list r

def size : bin_tree α → ℕ
| (leaf _) := 1
| (branch l r) := size l + size r

def from_list_lopsided : nonempty_list α → bin_tree α
| (nonempty_list.singleton x) := leaf x
| (nonempty_list.cons x xs)   := branch (leaf x) (from_list_lopsided xs)

lemma from_list_lopsided_to_list : Π (l : nonempty_list α), to_list (from_list_lopsided l) = l
| (nonempty_list.singleton x) := by reflexivity
| (nonempty_list.cons x xs)   :=
  begin
    unfold from_list_lopsided,
    unfold to_list,
    rewrite from_list_lopsided_to_list xs,
    reflexivity
  end

@[reducible] def lopsided (t : bin_tree α) : bin_tree α := from_list_lopsided t.to_list

lemma lopsided_idempotent (t : bin_tree α) : t.lopsided.lopsided = t.lopsided :=
  begin
    unfold lopsided,
    rewrite from_list_lopsided_to_list (to_list t)
  end

end bin_tree

end tqft.util.data.bin_tree