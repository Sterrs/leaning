import ..relations.between

-- Line segment
structure segment := (P₁ P₂ : point)
infix `↦`:50 := segment.mk

def has_length (s : segment) : Prop :=
s.P₁ ≠ s.P₂

-- If a segment has length then there is a line
-- which the endpoints lie on.
theorem extensible (s : segment)
(h : has_length s) :
∃ ℓ : line, s.P₁ ⊏ ℓ ∧ s.P₂ ⊏ ℓ :=
begin
  have := line_containing h,
  cases this with ℓ hℓ,
  existsi ℓ,
  assumption,
end

-- You lie on a segment iff you are between the endpoints
def lies_on_seg (A : point) (s : segment) : Prop :=
s.P₁∗A∗s.P₂
infix `⊏`:50 := lies_on_seg

-- A line and a segment intersect if they share a point
def intersect_seg (ℓ : line) (s : segment) : Prop :=
∃ (X : point), X ⊏ ℓ ∧ X ⊏ s

-- Two segments are disjoint if they do not share
-- a point
def disjoint (s t : segment) : Prop :=
¬(∃ P : point, P ⊏ s ∧ P ⊏ t)
