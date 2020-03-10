import .basic

-- Read disclaimer in basic.lean

-- 

-- The line between any two points is unique
axiom unique_line {a b : point}
{ℓ₁ ℓ₂ : line}:
(lies_on a ℓ₁ ∧ lies_on a ℓ₂ ∧ lies_on b ℓ₁ ∧ lies_on b ℓ₂)
→ (ℓ₁ = ℓ₂) ∨ (a = b)

-- There exist two points on a line
-- WARNING: This is wrong, a ≠ b should be output
axiom two_points (ℓ : line) :
∃ (a b : point), lies_on a ℓ ∧ lies_on b ℓ

-- Concept of three points being collinear
def collinear (a b c : point) : Prop :=
∃ (ℓ : line), lies_on a ℓ ∧ lies_on b ℓ ∧ lies_on c ℓ

-- There exist three points not all on the same line
axiom noncoll3 :
∃ (a b c : point), ¬ collinear a b c

-- Two lines intersect if they share a point
def intersect (ℓ₁ ℓ₂ : line) : Prop :=
∃ (p : point), lies_on p ℓ₁ ∧ lies_on p ℓ₂

-- Two lines are parallel if they do not intersect
-- TODO: Should equal lines be parallel?
def parallel (ℓ₁ ℓ₂ : line) : Prop :=
¬ intersect ℓ₁ ℓ₂

-- A line and a segment intersect if they share a point
def intersect_seg (ℓ : line) (s : segment) : Prop :=
∃ (p : point), lies_on p ℓ ∧ lies_on_seg p s

-- Pasch's axiom
-- If a line cuts a triangle once, it must cut
-- it again
axiom pasch {ℓ : line} {a b c : point}
(nonco : ¬ collinear a b c)
(h : intersect_seg ℓ ⟨a,b⟩) :
intersect_seg ℓ ⟨b, c⟩ ∨ intersect_seg ℓ ⟨c, a⟩


-- There's a unique line through p parallel to ℓ
-- This should allow us to prove the parallel postulate.
axiom euclid_exist (ℓ : line) (p : point)
(h : ¬ lies_on p ℓ) :
∃ (a : line), lies_on p a ∧ parallel ℓ a
axiom euclid_unique (ℓ₁ ℓ₂ l : line) (p : point)
(h : ¬ lies_on p l) (ha : lies_on p ℓ₁ ∧ parallel ℓ₁ l)
(hb : lies_on p ℓ₂ ∧ parallel ℓ₂ l) :
ℓ₁ = ℓ₂
