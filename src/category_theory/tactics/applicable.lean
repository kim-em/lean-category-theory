-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic


def applicable_attribute : user_attribute := {
  name := `applicable,
  descr := "A lemma that should be applied to a goal whenever possible."
}

run_cmd attribute.register `applicable_attribute

/- Try to apply one of the given lemas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic unit
| []      := failed
| (c::cs) := (mk_const c >>= fapply /->> trace ("applying " ++ to_string c)-/) <|> any_apply cs

meta def applicable : tactic unit :=
do cs ← attribute.get_instances `applicable,
   any_apply cs

attribute [applicable] funext
attribute [applicable] subtype.eq

@[applicable] lemma {u v} pairs_componentwise_equal {α : Type u} {β : Type v} { X Y : α × β } ( p1 : X.1 = Y.1 ) ( p2 : X.2 = Y.2 ) : X = Y := ♯
@[applicable] lemma {u v} dependent_pair_equality {α : Type u} {Z : α → Type v} { X Y : Σ a : α, Z a } ( p1 : X.1 = Y.1 ) ( p2 : @eq.rec α X.1 Z X.2 Y.1 p1 = Y.2 ) : X = Y := ♯
@[applicable] lemma {u} punit_equality ( X Y : punit.{u} ) : X = Y := ♯
@[applicable] lemma {u} plift_equality { α : Sort u } ( X Y : plift α ) ( p : X.down = Y.down ) : X = Y := ♯
@[applicable] lemma {u v} ulift_equality { α : Type v } ( X Y : ulift.{u v} α ) ( p : X.down = Y.down ) : X = Y := ♯
