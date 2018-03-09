import tactic.interactive

structure S :=
(x : ℕ)

example (a b : S) (p : a = b) : a.x = b.x := by cc
