import .intersect

-- DEFINITIONS

-- Two lines are parallel if they are equal or do not
-- intersect
def parallel (ℓ₁ ℓ₂ : line) : Prop :=
ℓ₁ = ℓ₂ ∨ ¬ intersect ℓ₁ ℓ₂
infix `∥`:50 := parallel

-- THEOREMS

-- Show that the parallel relation is symmetric
@[simp, symm]
theorem parallel_symm {ℓ₁ ℓ₂ : line} :
ℓ₁ ∥ ℓ₂ → ℓ₂ ∥ ℓ₁ :=
begin
  assume h,
  cases h with heq nin,
  left, symmetry, assumption,

  right,
  assume hi,
  have := intersect_symm hi,
  contradiction,
end
