-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

definition {u v} transport {A : Type u} { P : A → Type v} {x y : A} (u : P x) (p : x = y) : P y :=
by induction p; exact u