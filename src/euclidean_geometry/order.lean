import .basic

-- Read disclaimer in basic.lean

-- Axioms relating to the order of points on a
-- line

-- If B is between A and C then B is between
-- C and A
axiom between_symm {a b c : point} : between a b c →
between c b a

-- If B is between A and C then B lies on any line
-- A and C both lie on
-- This could be restated in a number of ways
axiom between_lies {a b c : point} {ℓ : line}
(h : between a b c) (ha : lies_on a ℓ)
(hb : lies_on b ℓ) : lies_on c ℓ

-- There is certainly a point between any distinct
-- two other points
axiom point_between {a c : point} (h : a ≠ c) :
∃ b : point, between a b c

-- If B is between A and C then
-- A is not between B and C and
-- C is not between A and B
axiom unique_order {a b c : point} :
between a b c → ¬ (between b a c) ∧ ¬ (between a c b)
