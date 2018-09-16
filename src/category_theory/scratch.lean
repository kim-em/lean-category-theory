import tactic.tidy
import tactic.linarith

def T : fin 2 → Type := ([ℕ, ℤ].to_array).data
def X : T ⟨ 0, by linarith ⟩ := begin show ℕ, exact 1 end
def Y : T ⟨ 1, by linarith ⟩ := begin show ℤ, exact -1 end

def S : Π n : fin 2, T n
| ⟨ 0, _ ⟩ := X
| ⟨ 1, _ ⟩ := Y
| ⟨ n + 2, _ ⟩ := by exfalso; linarith
