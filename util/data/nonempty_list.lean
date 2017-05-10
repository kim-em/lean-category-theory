namespace tqft.util.data.nonempty_list

universe u
variable {α : Type u}

-- structure nonempty_list (α : Type u) :=
--   (head : α)
--   (tail : list α)

inductive nonempty_list (α : Type u)
| singleton : α → nonempty_list
| cons : α → nonempty_list → nonempty_list

namespace nonempty_list

-- def singleton : α → nonempty_list α := λ x, { head := x, tail := [] }

@[reducible] def head : nonempty_list α → α
| (nonempty_list.singleton x) := x
| (nonempty_list.cons x _)    := x

@[reducible] def to_list : nonempty_list α → list α
| (singleton x) := [x]
| (cons x xs)   := x :: to_list xs

@[reducible] def tail : nonempty_list α → list α
| (singleton _) := []
| (cons _ xs)   := to_list xs

-- def append (xs : nonempty_list α) (ys : nonempty_list α) : nonempty_list α := {
--   head := xs.head,
--   tail := xs.tail ++ ys.to_list
-- }

def append : nonempty_list α → nonempty_list α → nonempty_list α
| (singleton x) ys := cons x ys
| (cons x xs)   ys := cons x (append xs ys)

instance : has_append (nonempty_list α) := ⟨ append ⟩

-- lemma append_assoc : Π (xs ys zs : nonempty_list α), append (append xs ys) zs = append xs (append ys zs) :=
-- begin
--   intros,
--   unfold append,
--   simp
-- end

@[simp] lemma singleton_append (x : α) (xs : nonempty_list α) : singleton x ++ xs = cons x xs :=
rfl

@[simp] lemma cons_append (x : α) (xs : nonempty_list α) (ys : nonempty_list α) : cons x xs ++ ys = cons x (xs ++ ys) :=
rfl

lemma append_assoc (xs ys zs : nonempty_list α) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
by induction xs; simph

end nonempty_list

end tqft.util.data.nonempty_list