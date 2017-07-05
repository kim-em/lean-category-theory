-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .transport .tidy

namespace tactic
meta def its (e : expr) (discharger : tactic unit): tactic unit := `[refine (transport %%e _)] <|> `[refine (cast _ %%e)] >> discharger
end tactic

open tactic
open interactive
open interactive.types

namespace tactic.interactive
meta def its (q : parse texpr) : tactic unit := i_to_expr ``(%%q) >>= λ e, tactic.its e (try tidy)
end tactic.interactive

lemma foo : nat :=
begin
its "a",
end