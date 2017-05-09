import ..bin_tree
import ..nonempty_list

open tqft.util.data.nonempty_list
open tqft.util.data.bin_tree
open tqft.util.data.bin_tree.bin_tree

universes u v

variable {α : Type u}

-- https://ncatlab.org/nlab/show/Mac+Lane%27s+proof+of+the+coherence+theorem+for+monoidal+categories

-- TODO(tim): do we really need two definitions of the congruence closure or can we just delete this one?
inductive cong_clos' (R : bin_tree α → bin_tree α → Type u) : bin_tree α → bin_tree α → Type u
| lift : Π s t, R s t → cong_clos' s t
| refl : Π t, cong_clos' t t
| trans : Π r s t, cong_clos' r s → cong_clos' s t → cong_clos' r t
| cong : Π l₁ r₁ l₂ r₂, cong_clos' l₁ l₂ → cong_clos' r₁ r₂ → cong_clos' (branch l₁ r₁) (branch l₂ r₂)

namespace cong_clos'

variable {R : bin_tree α → bin_tree α → Type u}

def sym (R_sym : Π s t, R s t → R t s)
    : Π {s t}, cong_clos' R s t → cong_clos' R t s
| ._ ._ (lift _ _ p)       := lift _ _ (R_sym _ _ p)
| ._ ._ (refl ._ t)        := refl R t
| ._ ._ (trans _ _ _ p q)  := trans _ _ _ (sym q) (sym p)
| ._ ._ (cong _ _ _ _ l r) := cong _ _ _ _ (sym l) (sym r)

def transport {S : bin_tree α → bin_tree α → Type u} (f : Π s t, R s t → S s t)
    : Π {s t}, cong_clos' R s t → cong_clos' S s t
| ._ ._ (lift _ _ p)       := lift _ _ (f _ _ p)
| ._ ._ (refl ._ t)        := refl S t
| ._ ._ (trans _ _ _ p q)  := trans _ _ _ (transport p) (transport q)
| ._ ._ (cong _ _ _ _ l r) := cong _ _ _ _ (transport l) (transport r)

lemma respects_to_list (R_to_list : Π s t, R s t → s.to_list = t.to_list)
    : Π {s t}, cong_clos' R s t → s.to_list = t.to_list
| ._ ._ (lift _ _ p)           := R_to_list _ _ p
| ._ ._ (refl ._ _)            := eq.refl _
| ._ ._ (trans _ _ _ p q)      := eq.trans (respects_to_list p) (respects_to_list q)
| ._ ._ (cong l₁ r₁ l₂ r₂ l r) :=
    begin
      unfold bin_tree.to_list,
      rewrite (respects_to_list l),
      rewrite (respects_to_list r)
    end

end cong_clos'

inductive cong_clos_step (R : bin_tree α → bin_tree α → Type u) : bin_tree α → bin_tree α → Type u
| lift  : Π s t, R s t → cong_clos_step s t
| left  : Π l₁ l₂ r, cong_clos_step l₁ l₂ → cong_clos_step (branch l₁ r) (branch l₂ r)
| right : Π l r₁ r₂, cong_clos_step r₁ r₂ → cong_clos_step (branch l r₁) (branch l r₂)

namespace cong_clos_step

variable {R : bin_tree α → bin_tree α → Type u}

-- the equation compiler somehow can't handle the next definitions ~> turn it off
-- TODO(tim): report bug
set_option eqn_compiler.lemmas false

def sym (R_sym : Π s t, R s t → R t s)
    : Π {s t}, cong_clos_step R s t → cong_clos_step R t s
| ._ ._ (lift _ _ p)    := lift _ _ (R_sym _ _ p)
| ._ ._ (left _ _ _ l)  := left _ _ _ (sym l)
| ._ ._ (right _ _ _ r) := right _ _ _ (sym r)

def transport {S : bin_tree α → bin_tree α → Type u} (f : Π s t, R s t → S s t)
    : Π {s t}, cong_clos_step R s t → cong_clos_step S s t
| ._ ._ (lift _ _ p)    := lift _ _ (f _ _ p)
| ._ ._ (left _ _ _ l)  := left _ _ _ (transport l)
| ._ ._ (right _ _ _ r) := right _ _ _ (transport r)

lemma respects_to_list (R_to_list : Π s t, R s t → s.to_list = t.to_list)
    : Π {s t}, cong_clos_step R s t → s.to_list = t.to_list
| ._ ._ (lift _ _ p)    := R_to_list _ _ p
| ._ ._ (left _ _ _ l)  := by unfold bin_tree.to_list; rewrite (respects_to_list l)
| ._ ._ (right _ _ _ r) := by unfold bin_tree.to_list; rewrite (respects_to_list r)

lemma respects_lopsided
    (R_to_list : Π s t, R s t → s.to_list = t.to_list)
    {s t} (p : cong_clos_step R s t)
    : s.lopsided = t.lopsided
  := by unfold lopsided; rewrite respects_to_list R_to_list p

set_option eqn_compiler.lemmas true

end cong_clos_step

-- smallest reflexive, transitive, congruent (but not necessarily symmetric) relation that includes R
inductive cong_clos (R : bin_tree α → bin_tree α → Type u) : bin_tree α → bin_tree α → Type u
| refl : Π t, cong_clos t t
| step : Π r s t, cong_clos_step R r s → cong_clos s t → cong_clos r t

namespace cong_clos

variable {R : bin_tree α → bin_tree α → Type u}

open cong_clos_step

def lift {s t : bin_tree α} (p : R s t) : cong_clos R s t :=
  step _ _ _ (cong_clos_step.lift _ _ p) (refl R _)

def trans : Π {r s t : bin_tree α}, cong_clos R r s → cong_clos R s t → cong_clos R r t
| ._ ._ _ (refl ._ t)       qs := qs
| ._ ._ _ (step _ _ _ p ps) qs := step _ _ _ p (trans ps qs)

lemma trans_refl_right : Π {s t : bin_tree α} (p : cong_clos R s t), trans p (refl R t) = p
| ._ ._ (refl ._ t)       := by reflexivity
| ._ ._ (step _ _ _ p ps) := by unfold trans; rewrite (trans_refl_right ps)

def inject_left (r : bin_tree α) : Π {l₁ l₂ : bin_tree α}, cong_clos R l₁ l₂ → cong_clos R (branch l₁ r) (branch l₂ r)
| ._ ._ (refl ._ t)       := refl R _
| ._ ._ (step _ _ _ p ps) := step _ _ _ (left _ _ _ p) (inject_left ps)

def inject_right (l : bin_tree α) : Π {r₁ r₂ : bin_tree α}, cong_clos R r₁ r₂ → cong_clos R (branch l r₁) (branch l r₂)
| ._ ._ (refl ._ _)       := refl R _
| ._ ._ (step _ _ _ p ps) := step _ _ _ (right _ _ _ p) (inject_right ps)

def cong {l₁ l₂ r₁ r₂ : bin_tree α} (l : cong_clos R l₁ l₂) (r : cong_clos R r₁ r₂) : cong_clos R (branch l₁ r₁) (branch l₂ r₂) :=
  trans (inject_left _ l) (inject_right _ r)

def convert : Π (s t : bin_tree α), cong_clos' R s t → cong_clos R s t
| ._ ._ (cong_clos'.refl ._ _)        := refl R _
| ._ ._ (cong_clos'.lift _ _ p)       := lift p
| ._ ._ (cong_clos'.trans _ _ _ p q)  := trans (convert _ _ p) (convert _ _ q)
| ._ ._ (cong_clos'.cong _ _ _ _ l r) := cong (convert _ _ l) (convert _ _ r)

def sym_helper (R_sym : Π s t, R s t → R t s)
    : Π {s t u}, cong_clos R s t → cong_clos R s u → cong_clos R t u
| ._ ._ _ (refl ._ t)       qs := qs
| ._ ._ _ (step _ _ _ p ps) qs := sym_helper ps (step _ _ _ (cong_clos_step.sym R_sym p) qs)

def sym (R_sym : Π s t, R s t → R t s) {s t} (ps : cong_clos R s t) : cong_clos R t s :=
  sym_helper R_sym ps (refl R _)

def transport {S : bin_tree α → bin_tree α → Type u} (f : Π s t, R s t → S s t)
    : Π {s t}, cong_clos R s t → cong_clos S s t
| ._ ._ (refl ._ t)       := refl S t
| ._ ._ (step _ _ _ p ps) := step _ _ _ (cong_clos_step.transport f p) (transport ps)

lemma respects_to_list (R_to_list : Π s t, R s t → s.to_list = t.to_list)
    : Π {s t}, cong_clos R s t → s.to_list = t.to_list
| ._ ._ (refl ._ t)       := by reflexivity
| ._ ._ (step r s t p ps) :=
  begin
    transitivity,
      exact (cong_clos_step.respects_to_list R_to_list p),
      exact (respects_to_list ps)
  end

lemma respects_lopsided
    (R_to_list : Π s t, R s t → s.to_list = t.to_list)
    {s t} (p : cong_clos R s t)
    : s.lopsided = t.lopsided
  := by unfold lopsided; rewrite respects_to_list R_to_list p

end cong_clos