noncomputable theory

-- A point is a basic object
axiom point : Type

-- Basic definitions & axioms
-- See https://en.wikipedia.org/wiki/Hilbert's_axioms

-- A line is a basic object
axiom line : Type

-- Relation between a point and a line
axiom lies_on : point → line → Prop
infix `⊏`:50 := lies_on

-- Given two distinct points there exists a line that they
-- both lie on.
axiom line_containing {A B : point} (distinct : A ≠ B) :
∃ (ℓ : line), A ⊏ ℓ ∧ B ⊏ ℓ
-- The line between any two points is unique
axiom line_unique {A B : point} {ℓ₁ ℓ₂ : line}:
(A ⊏ ℓ₁ ∧ A ⊏ ℓ₂ ∧ B ⊏ ℓ₁ ∧ B ⊏ ℓ₂)
→ (ℓ₁ = ℓ₂) ∨ (A = B)

-- Use line_unique and distinctness of points
-- to prove two lines are equal
theorem lines_equal {A B : point} {ℓ₁ ℓ₂ : line}
(distinct : A ≠ B)
(h : A ⊏ ℓ₁ ∧ A ⊏ ℓ₂ ∧ B ⊏ ℓ₁ ∧ B ⊏ ℓ₂) :
ℓ₁ = ℓ₂ :=
begin
  have := line_unique h,
  cases this with hleq hpeq,
    assumption,
  contradiction,
end

open classical

section
variables {A B : point} (distinct : A≠B)
include A B distinct
noncomputable def line_through : line :=
some (line_containing distinct)

theorem on_line_through1 :
A⊏(line_through distinct)  :=
begin
  unfold line_through,
  have he := some_spec (line_containing distinct),
  exact he.left,
end

theorem on_line_through2 :
B⊏(line_through distinct)  :=
begin
  unfold line_through,
  have he := some_spec (line_containing distinct),
  exact he.right,
end
end

-- There exist two points on a line
axiom two_points (ℓ : line) :
∃ (X Y : point), X ≠ Y ∧ X ⊏ ℓ ∧ Y ⊏ ℓ
