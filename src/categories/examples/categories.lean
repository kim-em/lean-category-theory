import category_theory.functor

universes u

namespace category_theory

def Small_Category : Type (u+1) := Σ C : Type u, small_category C
instance (𝒞 : Small_Category) : small_category (𝒞.1) := 𝒞.2

instance : category Small_Category :=
{ Hom     := λ 𝒞 𝒟, 𝒞.1 ↝ 𝒟.1,
  id      := λ 𝒞, (functor.id 𝒞.1),
  comp    := λ _ _ _ F G, F ⋙ G,
  id_comp := sorry,
  comp_id := sorry,
  assoc   := sorry }

end category_theory