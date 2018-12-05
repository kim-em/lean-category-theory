import category_theory.isomorphism
import category_theory.types

universes u v

def isos (C : Type u) := C

open category_theory

instance category_isos {C : Type u} [category.{u v} C] : category (isos C) :=
{ hom := λ X Y, @iso C _ X Y,
  id := iso.refl,
  comp := λ X Y Z, iso.trans }

instance category_isos_type : large_category (isos (Type u)) :=
by apply_instance

@[extensionality] lemma monoid.ext {α : Type u} (m n : monoid α)
  (mul : ∀ x y : α, (by haveI := m; exact x * y) = (by haveI := n; exact x * y)) : m = n :=
begin
  tactic.unfreeze_local_instances,
  induction m, induction n,
  congr,
  { ext x y,
    exact mul x y },
  { dsimp at *,
    rw ← n_one_mul m_one,
    rw ← mul,
    erw m_mul_one n_one },
end

def monoid_type_constructor : isos (Type u) ⥤ Type u :=
{ obj := monoid,
  map := λ α β f m,
  { one := f.hom (by resetI; exact 1),
      mul := λ x y, begin resetI, exact f.hom (f.inv x * f.inv y) end,
      one_mul := sorry,
      mul_one := sorry,
      mul_assoc := sorry },
  }

def monoid_type_constructor_indirection (α : Type u) : monoid α = monoid_type_constructor.obj α := rfl

def monoid_transport {α β : Type u} (f : α ≅ β) (m : monoid α) : monoid β :=
begin
  -- I'd like to prove this by:
  -- iso_induction f,
  -- exact m

  -- This tactic doesn't exist yet, but 'just' needs to do:
  rw monoid_type_constructor_indirection α at m,
  replace m := monoid_type_constructor.map f m,
  rw ← monoid_type_constructor_indirection β at m,
  clear f,
  clear α,

  exact m,
end
