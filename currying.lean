-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .natural_transformation
import .equivalence
import .products.bifunctors

open tqft.categories
open tqft.categories.isomorphism
open tqft.categories.functor
open tqft.categories.equivalence

namespace tqft.categories.natural_transformation

-- theorem {u1 v1 u2 v2 u3 v3} Currying_for_functors
--   ( C : Category.{u1 v1} )
--   ( D : Category.{u2 v2} )
--   ( E : Category.{u3 v3} ) :
--   Equivalence (FunctorCategory C (FunctorCategory D E)) (FunctorCategory (C × D) E) := 
--   {
--     functor := 
--     {
--       onObjects     := λ F, {
--         onObjects     := λ X, (F.onObjects X.1).onObjects X.2,
--         onMorphisms   := λ X Y f, begin
--                                    tidy,
--                                    note p := F.onMorphisms fst_2, 
--                                    note q := p.components snd, 
--                                    note r := (F.onObjects fst_1).onMorphisms snd_2,
--                                    exact E.compose q r,
--                                   end,
--         identities    := ♯,
--         functoriality := ♯
--       },
--       onMorphisms   := λ F G T, {
--         components := begin
--                         tidy,
--                         exact (T.components _).components _,
--                       end,       -- PROJECT really we should only have to specify this; everything else is determined
--         naturality := begin
--                         tidy,
--                         rewrite E.associativity,
--                         rewrite (T.components fst).naturality snd_2,
--                         rewrite - E.associativity,
--                         rewrite - E.associativity,
--                         note p := T.naturality fst_2,
--                         note p' := congr_arg NaturalTransformation.components p,
--                         note r' := congr_fun p' snd_1,
--                         tidy,
--                         rewrite r',
--                       end
--       },
--       identities    := ♯,
--       functoriality := ♯
--     },
--     inverse := {
--       onObjects     := λ F: Functor (C × D) E, {
--         onObjects     := λ X, {
--           onObjects     := λ Y, F (X, Y),
--           onMorphisms   := λ Y Y' g, F.onMorphisms (C.identity X, g),
--           identities    := ♯,
--           functoriality := ♯
--         },
--         onMorphisms   := λ X X' f, {
--           components := λ Y, F.onMorphisms (f, D.identity Y),
--           naturality := ♯
--         },
--         identities    := ♯,
--         functoriality := ♯
--       },
--       onMorphisms   := λ F G T, {
--         components := λ X, {
--           components := λ Y, T.components (X, Y),
--           naturality := ♯
--         },
--         naturality := ♯
--       },
--       identities    := ♯,
--       functoriality := ♯
--     },
--     isomorphism_1 := begin tidy, admit end,
--     isomorphism_2 := begin tidy, admit end
--   }

end tqft.categories.natural_transformation