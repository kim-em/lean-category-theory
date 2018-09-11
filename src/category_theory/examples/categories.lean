import category_theory.functor

universes u v

namespace category_theory

structure Category : Type (max (u+1) (v+1)) :=
 (C : Type u)
 [𝒞 : category.{u v} C]

instance category_of_Category (𝒞 : Category) : category (𝒞.C) := 𝒞.𝒞

instance CAT : category.{(max (u+1) (v+1)) (max u v)} Category :=
{ hom     := λ 𝒞 𝒟, 𝒞.C ⥤ 𝒟.C,
  id      := λ 𝒞, (functor.id 𝒞.C),
  comp    := λ _ _ _ F G, F ⋙ G,
  id_comp' := begin tidy, cases f, dsimp [functor.comp], refl end,
  comp_id' := begin tidy, cases f, dsimp [functor.comp], refl end,
  assoc'   := begin tidy, end }

end category_theory