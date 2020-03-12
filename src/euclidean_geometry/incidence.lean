import .basic

-- The line between any two points is unique
axiom line_unique {A B : point} {ℓ₁ ℓ₂ : line}:
(A ⊏ ℓ₁ ∧ A ⊏ ℓ₂ ∧ B ⊏ ℓ₁ ∧ B ⊏ ℓ₂)
→ (ℓ₁ = ℓ₂) ∨ (A = B)

-- There exist two points on a line
-- WARNING: This is wrong, a ≠ b should be output
axiom two_points (ℓ : line) :
∃ (X Y : point), X ⊏ ℓ ∧ Y ⊏ ℓ

-- Concept of three points being collinear
def collinear (A B C : point) : Prop :=
∃ (ℓ : line), A ⊏ ℓ ∧ B ⊏ ℓ ∧ C ⊏ ℓ

-- There exist three points not all on the same line
axiom noncoll3 :
∃ (X Y Z : point),
(X ≠ Y) ∧ (Y ≠ Z) ∧ (Z ≠ X) ∧ ¬ collinear X Y Z

-- Two lines intersect if they share a point
def intersect (ℓ₁ ℓ₂ : line) : Prop :=
∃ (X : point), X ⊏ ℓ₁ ∧ X ⊏ ℓ₂

-- Two lines are parallel if they do not intersect
-- TODO: Should equal lines be parallel?
def parallel (ℓ₁ ℓ₂ : line) : Prop :=
ℓ₁ = ℓ₂ ∨ ¬ intersect ℓ₁ ℓ₂
infix `∥`:50 := parallel

-- A line and a segment intersect if they share a point
def intersect_seg (ℓ : line) (s : segment) : Prop :=
∃ (X : point), X ⊏ ℓ ∧ X ⊏ s

-- Pasch's axiom
-- If a line cuts a triangle once, it must cut
-- it again
axiom pasch {ℓ : line} {A B C : point}
(nonco : ¬ collinear A B C)
(h : intersect_seg ℓ ⟨A, B⟩) :
intersect_seg ℓ ⟨B, C⟩ ∨ intersect_seg ℓ ⟨C, A⟩


-- There's a unique line through p parallel to ℓ
-- This should allow us to prove the parallel postulate.
axiom euclid_exist {ℓ : line} {P : point}
(h : ¬ P ⊏ ℓ) :
∃ (a : line), P ⊏ a ∧ ℓ ∥ a
axiom euclid_unique {a₁ a₂ ℓ : line} {P : point}
(h : ¬ P ⊏ ℓ) (ha : P ⊏ a₁ ∧ a₁ ∥ ℓ)
(hb : P ⊏ a₂ ∧ a₂ ∥ ℓ) :
a₁ = a₂
