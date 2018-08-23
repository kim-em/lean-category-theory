import .coyoneda

open category_theory

universes u₁ v₁

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
include 𝒞

class representable (F : C ↝ (Type v₁)) := 
(c : C)
(Φ : F ⇔ ((coyoneda C) c))