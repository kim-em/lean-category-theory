import category_theory.presheaves
import category_theory.limits.limits

universes u v

open category_theory
open category_theory.examples
open category_theory.limits
open category_theory.presheaves

namespace category_theory.presheaves.Presheaf

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def near (F : Presheaf.{u v} C) (x : F) : { U : open_set F.X // x ∈ U } ⥤ C :=
(full_subcategory_embedding (λ U : open_set F.X, x ∈ U)) ⋙ F.𝒪 

variable [has_colimits.{u v} C]

def stalk_at (F : Presheaf.{u v} C) (x : F.X) : C :=
colimit (F.near x)

end category_theory.presheaves.Presheaf
