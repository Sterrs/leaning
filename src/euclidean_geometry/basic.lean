-- A point is a basic object
axiom point : Type

-- Basic definitions & axioms
-- See https://en.wikipedia.org/wiki/Hilbert's_axioms
-- TODO: Document the axioms properly in LaTeX

-- Ternary relation for points
axiom between (A B C : point) :  Prop
notation A `∗` B `∗` C := between A B C

-- A line is a basic object
axiom line : Type

-- Relation between a point and a line
axiom lies_on : point → line → Prop
infix `⊏`:50 := lies_on

-- Given two distinct points there exists a line that they
-- both lie on.
axiom line_containing {A B : point} (distinct : A ≠ B) :
∃ (ℓ : line), A ⊏ ℓ ∧ B ⊏ ℓ

#check @line_containing

-- Two lines are equal iff they share every point
axiom line_eq (ℓ₁ ℓ₂ : line) :
ℓ₁ = ℓ₂ ↔
∀ (X : point) (h : X ⊏ ℓ₁), X ⊏ ℓ₂

-- Angle
structure angle := (ℓ₁ ℓ₂ : line)

-- Line segment
structure segment := (P₁ P₂ : point)

-- You lie on a segment iff you are between the endpoints
def lies_on_seg (A : point) (s : segment) : Prop :=
s.P₁ ∗ A ∗ s.P₂
infix `⊏`:50 := lies_on_seg
