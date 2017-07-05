-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

open tactic

-- FIXME this should not be here, but I don't know how to make 'automatic_inductions' updateable. Use attributes?
inductive Two : Type
| _0 : Two
| _1 : Two
