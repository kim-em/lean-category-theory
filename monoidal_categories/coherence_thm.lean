import .monoidal_category
import ..util.data.nonempty_list
import ..util.data.bin_tree
import ..util.data.bin_tree.cong_clos

open tqft.categories
open tqft.categories.monoidal_category
open tqft.util.data.nonempty_list
open tqft.util.data.bin_tree
open tqft.util.data.bin_tree.bin_tree

namespace tqft.categories.monoidal_category.coherence_thm

universes u v

variable {α : Type u}

inductive reassoc_dir_single_step : bin_tree α → bin_tree α → Type u
| rotate_right : Π r s t, reassoc_dir_single_step (branch (branch r s) t) (branch r (branch s t))

namespace reassoc_dir_single_step

lemma respects_to_list : Π (s t : bin_tree α), reassoc_dir_single_step s t → s.to_list = t.to_list
| ._ ._ (rotate_right _ _ _) :=
    begin
      unfold bin_tree.to_list,
      rewrite nonempty_list.append_assoc
    end

end reassoc_dir_single_step

@[reducible] def reassoc_dir_step : bin_tree α → bin_tree α → Type u :=
  cong_clos_step reassoc_dir_single_step

namespace reassoc_dir_step

lemma respects_lopsided {s t : bin_tree α} (p : reassoc_dir_step s t) : s.lopsided = t.lopsided :=
  cong_clos_step.respects_lopsided reassoc_dir_single_step.respects_to_list p

end reassoc_dir_step

@[reducible] def reassoc_dir : bin_tree α → bin_tree α → Type u :=
  cong_clos reassoc_dir_single_step

@[reducible] def reassoc_dir' : bin_tree α → bin_tree α → Type u :=
  cong_clos' reassoc_dir_single_step

namespace reassoc_dir

@[reducible] def refl (t : bin_tree α) : reassoc_dir t t := cong_clos.refl _ t

def rotate_right (r s t : bin_tree α) : reassoc_dir (branch (branch r s) t) (branch r (branch s t)) :=
  cong_clos.lift (reassoc_dir_single_step.rotate_right _ _ _)

def lopsided_combine : Π (xs ys : nonempty_list α),
    reassoc_dir (branch (from_list_lopsided xs) (from_list_lopsided ys)) (from_list_lopsided (xs ++ ys))
| (nonempty_list.singleton x) ys := refl _
| (nonempty_list.cons x xs)   ys :=
  begin
    simp, unfold from_list_lopsided,
    apply cong_clos.trans,
      apply rotate_right,
      apply cong_clos.cong,
        apply reassoc_dir.refl,
        apply lopsided_combine
  end

def reassoc_lopsided : Π (t : bin_tree α), reassoc_dir t t.lopsided
| (leaf x)     := refl _
| (branch l r) :=
  begin
    apply cong_clos.trans,
      apply cong_clos.cong,
        apply reassoc_lopsided,
        apply reassoc_lopsided,
    apply lopsided_combine
  end

lemma reassoc_already_lopsided :
    Π (l : nonempty_list α),
    reassoc_lopsided (bin_tree.from_list_lopsided l) == refl (bin_tree.from_list_lopsided l)
| (nonempty_list.singleton x) := by reflexivity
| (nonempty_list.cons x xs)   :=
    calc
          cong_clos.trans
            (cong_clos.inject_right _ (reassoc_lopsided (from_list_lopsided xs)))
            (refl (branch (leaf x) (from_list_lopsided (to_list (from_list_lopsided xs)))))
        = cong_clos.inject_right (leaf x) (reassoc_lopsided (from_list_lopsided xs))
        : by apply cong_clos.trans_refl_right
    ... == cong_clos.inject_right (leaf x) (refl (from_list_lopsided xs))
        : begin
            congr_args,
              unfold lopsided, rewrite from_list_lopsided_to_list,
              apply reassoc_already_lopsided
          end
    ... == refl (branch (leaf x) (from_list_lopsided xs))
        : by reflexivity

lemma respects_to_list {s t : bin_tree α} (p : reassoc_dir s t) : s.to_list = t.to_list :=
  cong_clos.respects_to_list reassoc_dir_single_step.respects_to_list p

lemma respects_lopsided {s t : bin_tree α} (p : reassoc_dir s t) : s.lopsided = t.lopsided :=
  cong_clos.respects_lopsided reassoc_dir_single_step.respects_to_list p

end reassoc_dir

inductive reassoc_single_step : bin_tree α → bin_tree α → Type u
| rotate_left  : Π r s t, reassoc_single_step (branch r (branch s t)) (branch (branch r s) t)
| rotate_right : Π r s t, reassoc_single_step (branch (branch r s) t) (branch r (branch s t))

@[reducible] def reassoc_step : bin_tree α → bin_tree α → Type u :=
  cong_clos_step reassoc_single_step

@[reducible] def reassoc : bin_tree α → bin_tree α → Type u :=
  cong_clos reassoc_single_step

namespace reassoc_single_step

def sym : Π (x y : bin_tree α), reassoc_single_step x y → reassoc_single_step y x
| ._ ._ (rotate_left  _ _ _) := rotate_right _ _ _
| ._ ._ (rotate_right _ _ _) := rotate_left  _ _ _

lemma respects_to_list : Π (s t : bin_tree α), reassoc_single_step s t → s.to_list = t.to_list
| ._ ._ (rotate_left _ _ _) :=
    begin
      unfold bin_tree.to_list,
      rewrite nonempty_list.append_assoc
    end
| ._ ._ (rotate_right _ _ _) :=
    begin
      unfold bin_tree.to_list,
      rewrite nonempty_list.append_assoc
    end

end reassoc_single_step

def reassoc_dir_to_reassoc_single_step : Π (s t : bin_tree α), reassoc_dir_single_step s t → reassoc_single_step s t
| ._ ._ (reassoc_dir_single_step.rotate_right s t u) := reassoc_single_step.rotate_right s t u

def reassoc_dir_to_reassoc : Π {s t : bin_tree α}, reassoc_dir s t → reassoc s t :=
  λ s t p, cong_clos.transport reassoc_dir_to_reassoc_single_step p

namespace reassoc

@[reducible] def refl (t : bin_tree α) : reassoc_dir t t := cong_clos.refl _ t

def sym : Π {x y : bin_tree α}, reassoc x y → reassoc y x :=
  λ x y, cong_clos.sym reassoc_single_step.sym

lemma respects_to_list : Π {s t : bin_tree α}, reassoc s t → s.to_list = t.to_list :=
  λ x y, cong_clos.respects_to_list reassoc_single_step.respects_to_list

def reassoc_lopsided : Π (t : bin_tree α), reassoc t t.lopsided :=
  λ t, reassoc_dir_to_reassoc (reassoc_dir.reassoc_lopsided t)

-- TODO: more economical construction (with fewer rotations)
def reassoc_tree : Π (r t : bin_tree α) (h : r.to_list = t.to_list), reassoc r t :=
begin
  intros,
  apply cong_clos.trans,
  apply reassoc_lopsided,
  -- TODO: doing `rewrite h` here doesn't work ~> report bug
  apply sym,
  unfold lopsided, rewrite h,
  apply reassoc_lopsided
end

end reassoc

section interpretation

parameter (C : Category.{u v})
parameter (M : MonoidalStructure C)

@[reducible] def tensor : C.Obj → C.Obj → C.Obj := λ X Y, M.tensor (X, Y)

local infixl `⟩C⟩`:60 := C.compose

local infix `⊗`:60 := tensor

-- this is better behaved wrt type inference than `M.tensor.onMorphisms` because no tuple has to be inferred
@[reducible] def tensor_homs : Π {W X Y Z : C.Obj}, C.Hom W X → C.Hom Y Z → C.Hom (W ⊗ Y) (X ⊗ Z) :=
  λ W X Y Z f g, M.tensor.onMorphisms (f, g)

local infix `⟨⊗⟩`:60 := tensor_homs

open cong_clos

@[reducible] def tensor_tree : bin_tree C.Obj → C.Obj
| (bin_tree.leaf A)     := A
| (bin_tree.branch l r) := tensor_tree l ⊗ tensor_tree r

def interpret_cong_clos'
    {R : bin_tree C.Obj → bin_tree C.Obj → Type u}
    (I : Π (Xs Ys : bin_tree C.Obj), R Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys))
    : Π {Xs Ys : bin_tree C.Obj}, cong_clos' R Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys)
| ._ ._ (cong_clos'.lift _ _ p)       := I _ _ p
| ._ ._ (cong_clos'.refl ._ t)        := C.identity _
| ._ ._ (cong_clos'.trans _ _ _ p q)  := C.compose (interpret_cong_clos' p) (interpret_cong_clos' q)
| ._ ._ (cong_clos'.cong _ _ _ _ l r) := M.tensor.onMorphisms (interpret_cong_clos' l, interpret_cong_clos' r)

-- the equation compiler somehow can't handle the next definitions ~> turn it off
-- TODO(tim): report bug
set_option eqn_compiler.lemmas false

-- TODO(tim): factor out I as a variable
def interpret_cong_clos_step
    {R : bin_tree C.Obj → bin_tree C.Obj → Type u}
    (I : Π (Xs Ys : bin_tree C.Obj), R Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys))
    : Π {Xs Ys : bin_tree C.Obj}, cong_clos_step R Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys)
| ._ ._ (cong_clos_step.lift x y p)      := I x y p
| ._ ._ (cong_clos_step.left l₁ l₂ r l)  := interpret_cong_clos_step l ⟨⊗⟩ C.identity (tensor_tree r)
| ._ ._ (cong_clos_step.right l r₁ r₂ r) := C.identity (tensor_tree l) ⟨⊗⟩ interpret_cong_clos_step r

set_option eqn_compiler.lemmas true

def interpret_cong_clos
    {R : bin_tree C.Obj → bin_tree C.Obj → Type u}
    (I : Π (Xs Ys : bin_tree C.Obj), R Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys))
    : Π {Xs Ys : bin_tree C.Obj}, cong_clos R Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys)
| ._ ._ (cong_clos.refl ._ t)      := C.identity _
| ._ ._ (cong_clos.step _ _ _ p q) := C.compose (interpret_cong_clos_step I p) (interpret_cong_clos q)

lemma interpret_cong_clos_functoriality
    {R : bin_tree C.Obj → bin_tree C.Obj → Type u}
    (I : Π (Xs Ys : bin_tree C.Obj), R Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys))
    : Π (Xs Ys Zs : bin_tree C.Obj) (ps : cong_clos R Xs Ys) (qs : cong_clos R Ys Zs),
      interpret_cong_clos I ps ⟩C⟩ interpret_cong_clos I qs = interpret_cong_clos I (cong_clos.trans ps qs)
| ._ ._ _ (cong_clos.refl ._ t)       qs := C.left_identity _
| ._ ._ _ (cong_clos.step _ _ _ p ps) qs :=
    begin
      unfold cong_clos.trans,
      unfold interpret_cong_clos,
      rewrite C.associativity,
      rewrite interpret_cong_clos_functoriality
    end

-- TODO(tim): move this somewhere else?
lemma functoriality_left
    (X Y Z A : C.Obj)
    (f : C.Hom X Y) (g : C.Hom Y Z)
    : (f ⟩C⟩ g) ⟨⊗⟩ C.identity A = (f ⟨⊗⟩ C.identity A) ⟩C⟩ (g ⟨⊗⟩ C.identity A) := ♮

lemma interpret_cong_clos_inject_left
    {R : bin_tree C.Obj → bin_tree C.Obj → Type u}
    (I : Π (Xs Ys : bin_tree C.Obj), R Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys))
    : Π (Xs Ys Zs : bin_tree C.Obj) (ps : cong_clos R Xs Ys),
      interpret_cong_clos I (inject_left Zs ps) = interpret_cong_clos I ps ⟨⊗⟩ C.identity (tensor_tree Zs)
| ._ ._ _ (cong_clos.refl ._ _)       := by {symmetry, apply M.tensor.identities}
| ._ ._ _ (cong_clos.step _ _ _ p ps) :=
  begin
    unfold inject_left,
    unfold interpret_cong_clos,
    rewrite functoriality_left,
    rewrite (interpret_cong_clos_inject_left _ _ _ ps),
    reflexivity
  end

-- TODO(tim): it would be cool if interpretation were a real functor from a suitable formal category

def interpret_reassoc_dir_single_step : Π (Xs Ys : bin_tree C.Obj), reassoc_dir_single_step Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys)
| ._ ._ (reassoc_dir_single_step.rotate_right s t u) := M.associator _ _ _

def interpret_reassoc_dir {Xs Ys : bin_tree C.Obj} : reassoc_dir Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys) :=
  interpret_cong_clos interpret_reassoc_dir_single_step

lemma interpret_reassoc_dir_functoriality
    {Xs Ys Zs : bin_tree C.Obj} (ps : reassoc_dir Xs Ys) (qs : reassoc_dir Ys Zs)
    : interpret_reassoc_dir ps ⟩C⟩ interpret_reassoc_dir qs = interpret_reassoc_dir (cong_clos.trans ps qs)
  := by apply interpret_cong_clos_functoriality

def interpret_reassoc_dir' {Xs Ys : bin_tree C.Obj} : reassoc_dir' Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys) :=
  interpret_cong_clos' interpret_reassoc_dir_single_step

def interpret_reassoc_dir_step {Xs Ys : bin_tree C.Obj} : reassoc_dir_step Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys) :=
  interpret_cong_clos_step interpret_reassoc_dir_single_step

def interpret_reassoc_single_step : Π (Xs Ys : bin_tree C.Obj), reassoc_single_step Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys)
| ._ ._ (reassoc_single_step.rotate_right s t u) := M.associator _ _ _
| ._ ._ (reassoc_single_step.rotate_left  s t u) := M.inverse_associator _ _ _

def interpret_reassoc {Xs Ys : bin_tree C.Obj} : reassoc Xs Ys → C.Hom (tensor_tree Xs) (tensor_tree Ys) :=
  interpret_cong_clos interpret_reassoc_single_step

@[reducible] def to_lopsided (t : bin_tree C.Obj) : C.Hom (tensor_tree t) (tensor_tree t.lopsided) :=
  interpret_reassoc_dir (reassoc_dir.reassoc_lopsided t)

-- TODO: generalize to cong_clos
def rewrite_source : Π {s₁ s₂ t : bin_tree α} (eq : s₁ = s₂), reassoc_dir s₁ t → reassoc_dir s₂ t
| _ ._ _ (eq.refl ._) p := p

-- TODO: generalize to cong_clos
def rewrite_target : Π {s t₁ t₂ : bin_tree α} (eq : t₁ = t₂), reassoc_dir s t₁ → reassoc_dir s t₂
| _ ._ _ (eq.refl ._) p := p

-- TODO: generalize to cong_clos
def rewrite_target_cong : Π {s t₁ t₂ : bin_tree α} (eq : t₁ = t₂) (p : reassoc_dir s t₁), rewrite_target eq p == p
| _ _ ._ (eq.refl ._) p := heq.refl _

@[reducible] def trans_lopsided' {s t : bin_tree α} (p : reassoc_dir s t) : reassoc_dir s t.lopsided :=
  cong_clos.trans p (reassoc_dir.reassoc_lopsided t)

-- all roads lead to rome
def trans_lopsided {s t : bin_tree α} (p : reassoc_dir s t) : reassoc_dir s s.lopsided :=
  rewrite_target (eq.symm (reassoc_dir.respects_lopsided p)) (trans_lopsided' p)

lemma trans_lopsided_heq {s t : bin_tree α} (p : reassoc_dir s t) : trans_lopsided p == trans_lopsided' p :=
  by apply rewrite_target_cong

lemma trans_lopsided_already_lopsided {s : bin_tree α} (p : reassoc_dir s s.lopsided) : trans_lopsided p == p :=
  calc
         rewrite_target (eq.symm (reassoc_dir.respects_lopsided p)) (cong_clos.trans p (reassoc_dir.reassoc_lopsided s.lopsided))
      == cong_clos.trans p (reassoc_dir.reassoc_lopsided s.lopsided)
      : by apply rewrite_target_cong
  ... == cong_clos.trans p (reassoc_dir.refl s.lopsided)
      : begin congr_args, rewrite lopsided_idempotent, apply reassoc_dir.reassoc_already_lopsided end
  ... = p
      : by apply trans_refl_right

@[reducible] def step_lopsided' {s t : bin_tree α} (p : reassoc_dir_step s t) : reassoc_dir s t.lopsided :=
  cong_clos.step _ _ _ p (reassoc_dir.reassoc_lopsided t)

def step_lopsided {s t : bin_tree α} (p : reassoc_dir_step s t) : reassoc_dir s s.lopsided :=
  rewrite_target (eq.symm (reassoc_dir_step.respects_lopsided p)) (step_lopsided' p)

lemma step_lopsided_heq {s t : bin_tree α} (p : reassoc_dir_step s t) : step_lopsided p == step_lopsided' p :=
  by apply rewrite_target_cong

-- -- TODO(tim): use well-founded induction once lean supports it
-- -- TODO(tim): why does lean complain that there are missing cases???
-- meta lemma directed_associator_coherence_thm :
--     Π (Xs Ys : bin_tree C.Obj) (e : Ys = Xs.lopsided)
--       (p q : reassoc_dir Xs Ys),
--       interpret_reassoc_dir p = interpret_reassoc_dir q
-- | (branch l r) ._ (eq.refl ._) (cong_clos.step ._ ._ ._ (cong_clos_step.left ._ lp ._ p) ps) (cong_clos.step ._ ._ ._ (cong_clos_step.left ._ lq ._ q) qs) :=
--     have H : Π (l' : bin_tree C.Obj) (f : reassoc_dir_step l l') (fs : reassoc_dir (branch l' r) (branch l r).lopsided),
--                interpret_reassoc_dir (step (branch l r) _ _ (cong_clos_step.left _ _ r f) fs) == 
--                (to_lopsided l ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ to_lopsided (branch l.lopsided r), from
--         λ l' f fs,
--         have e₀ : lopsided l = lopsided l', from
--           by {apply reassoc_dir_step.respects_lopsided, assumption},
--         have e₁ : lopsided (branch l r) = lopsided (branch l' r), from
--           by {apply reassoc_dir_step.respects_lopsided, apply cong_clos_step.left, assumption},
--         have e₂ : lopsided (branch l' r) = lopsided (branch (lopsided l') r), from
--           by {unfold lopsided, congr_args, unfold to_list, rewrite from_list_lopsided_to_list},
--         have e₃ : interpret_reassoc_dir fs == (interpret_reassoc_dir (reassoc_dir.reassoc_lopsided l') ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided (branch l'.lopsided r)), from
--             calc
--                   interpret_reassoc_dir fs
--                 == interpret_reassoc_dir (rewrite_target e₁ fs)
--                 :  by {congr_args, assumption, symmetry, apply rewrite_target_cong}
--             ... =  interpret_reassoc_dir (trans_lopsided (cong_clos.inject_left r (reassoc_dir.reassoc_lopsided l')))
--                 :  by apply directed_associator_coherence_thm (branch l' r) (branch l' r).lopsided (eq.refl _)
--             ... == interpret_reassoc_dir (trans_lopsided' (cong_clos.inject_left r (reassoc_dir.reassoc_lopsided l')))
--                 :  by {congr_args, assumption, apply trans_lopsided_heq}
--             ... =  interpret_reassoc_dir (cong_clos.inject_left r (reassoc_dir.reassoc_lopsided l')) ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided (branch l'.lopsided r))
--                 :  by {symmetry, apply interpret_reassoc_dir_functoriality}
--             ... =  (interpret_reassoc_dir (reassoc_dir.reassoc_lopsided l') ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided (branch l'.lopsided r))
--                 :  by {congr_args, apply interpret_cong_clos_inject_left},
--         calc
--                 (interpret_reassoc_dir_step f ⟨⊗⟩ C.identity _) ⟩C⟩ interpret_reassoc_dir fs
--             == (interpret_reassoc_dir_step f ⟨⊗⟩ C.identity _) ⟩C⟩ ((interpret_reassoc_dir (reassoc_dir.reassoc_lopsided l') ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided (branch l'.lopsided r)))
--             :  by {congr_args, cc, assumption}
--         ... == ((interpret_reassoc_dir_step f ⟨⊗⟩ C.identity _) ⟩C⟩ (interpret_reassoc_dir (reassoc_dir.reassoc_lopsided l') ⟨⊗⟩ C.identity (tensor_tree r))) ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided (branch l'.lopsided r))
--             :  ♮
--         ... == ((interpret_reassoc_dir_step f ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided l')) ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided (branch l'.lopsided r))
--             :  by rewrite functoriality_left
--         ... == (interpret_reassoc_dir (cong_clos.step _ _ _ f (reassoc_dir.reassoc_lopsided l')) ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided (branch l'.lopsided r))
--             :  by reflexivity
--         ... == (interpret_reassoc_dir (step_lopsided f) ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ interpret_reassoc_dir (reassoc_dir.reassoc_lopsided (branch l.lopsided r))
--             :  begin
--                  congr_args,
--                   {cc},
--                   {cc},
--                   {congr_args, cc, congr_args, cc, symmetry, apply step_lopsided_heq},
--                   {cc}
--                end
--         ... = (to_lopsided l ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ to_lopsided (branch l.lopsided r)
--             :  by {congr_args, congr_args, apply directed_associator_coherence_thm l l.lopsided (eq.refl _)},
--     eq_of_heq $
--     calc
--            interpret_reassoc_dir (step (branch l r) _ _ (cong_clos_step.left _ _ r p) ps)
--         == (to_lopsided l ⟨⊗⟩ C.identity (tensor_tree r)) ⟩C⟩ to_lopsided (branch l.lopsided r)
--         :  by apply H
--     ... == interpret_reassoc_dir (step (branch l r) _ _ (cong_clos_step.left _ _ r q) qs)
--         :  by {symmetry, apply H}
-- | (branch l r) Ys e (cong_clos.step ._ ._ ._ (cong_clos_step.right ._ ._ rp p) ps) (cong_clos.step ._ ._ ._ (cong_clos_step.right ._ ._ rq q) qs) := sorry
-- | (branch l r) Ys e (cong_clos.step ._ ._ ._ (cong_clos_step.left ._ lp ._ p) ps) (cong_clos.step ._ ._ ._ (cong_clos_step.right ._ ._ rq q) qs) := sorry
-- | (branch l r) Ys e (cong_clos.step ._ ._ ._ (cong_clos_step.right ._ ._ rp p) ps) (cong_clos.step ._ ._ ._ (cong_clos_step.left ._ lq ._ q) qs) := sorry
-- | (branch (branch x y) z) Ys e (cong_clos.step ._ ._ ._ (cong_clos_step.lift ._ ._ (reassoc_dir_single_step.rotate_right ._ ._ ._)) _) (cong_clos.step ._ _ ._ _ _) := sorry
-- | (branch (branch x y) z) Ys e (cong_clos.step ._ _ ._ _ _) (cong_clos.step ._ ._ ._ (cong_clos_step.lift ._ ._ (reassoc_dir_single_step.rotate_right ._ ._ ._)) _) := sorry
-- | Xs ._ e (cong_clos.refl ._ ._) (cong_clos.step ._ t' ._ q _) := sorry
-- | Xs ._ e (cong_clos.step ._ t' ._ p _) (cong_clos.refl ._ ._) := sorry
-- | Xs ._ e (cong_clos.refl ._ ._) (cong_clos.refl ._ ._) := sorry

end interpretation

end tqft.categories.monoidal_category.coherence_thm