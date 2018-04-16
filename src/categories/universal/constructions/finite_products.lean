-- PROJECT this has become nontrivial, because we're asserting that finite products can be indexed from the same universe level.
-- This requires us to use the fact that `fin n` is in level 0.
-- section
-- variable (C : Type (max (u+1) v))
-- variable [category C]

-- instance FiniteProducts_from_Products [has_Products C] : has_FiniteProducts C := {
--   product := λ _ _ f, has_Products.product f
-- }
-- instance FiniteCoproducts_from_Coproducts [has_Coproducts C] : has_FiniteCoproducts C := {
--   coproduct := λ _ _ f, has_Coproducts.coproduct f
-- }
-- end

-- PROJECT:
-- open nat

-- definition construct_finite_product (C : Category) [has_TerminalObject C] [has_BinaryProducts C]
--   : Π n : nat, Π (I : Type) (fin : Finite I) (p : fin.cardinality = n) (f : I → C.Obj), Product f
-- | 0        := λ {I : Type} [fin : Finite I] (p : fin.cardinality = 0) (f : I → C.Obj), {
--                 product       := terminal_object,
--                 projection    := begin intros, sorry end,
--                 map           := sorry,
--                 factorisation := sorry,
--                 uniqueness    := sorry
--              }
-- | (succ n) := sorry

-- instance FiniteProducts_from_BinaryProducts (C : Category) [has_TerminalObject C] [has_BinaryProducts C] : has_FiniteProducts C := {
--   product := λ {I : Type} [fin : Finite I] (f : I → C.Obj), construct_finite_product C fin.cardinality I fin by obviously' f
--}