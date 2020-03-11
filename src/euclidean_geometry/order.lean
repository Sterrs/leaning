import .basic

-- Axioms relating to the order of points on a
-- line

-- If B is between A and C then B is between
-- C and A
axiom between_symm {A B C : point} : between A B C →
between C B A

-- If B is between A and C then B lies on any line
-- A and C both lie on
-- This could be restated in a number of ways
axiom between_lies {A B C : point} {ℓ : line}
(h : between A B C) (ha : lies_on A ℓ)
(hb : lies_on B ℓ) : lies_on C ℓ

-- There is certainly a point between any distinct
-- two other points
axiom point_between {A C : point} (h : A ≠ C) :
∃ B : point, between A B C

-- If B is between A and C then
-- A is not between B and C and
-- C is not between A and B
axiom unique_order {A B C : point} :
between A B C → ¬ (between B A C) ∧ ¬ (between A C B)
