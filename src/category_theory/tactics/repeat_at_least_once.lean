-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

namespace tactic

meta def repeat_at_least_once ( t : tactic unit ) : tactic unit := t >> repeat t

namespace interactive
meta def repeat_at_least_once : itactic → tactic unit :=
tactic.repeat_at_least_once
end interactive

end tactic