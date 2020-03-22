import ..existence

-- DEFINITIONS

-- Two lines intersect if they share a point
def intersect (ℓ₁ ℓ₂ : line) : Prop :=
∃ (X : point), X ⊏ ℓ₁ ∧ X ⊏ ℓ₂

-- THEOREMS

-- Show that the intersect relation is symmetric
@[simp, symm]
theorem intersect_symm {ℓ₁ ℓ₂ : line} :
intersect ℓ₁ ℓ₂ → intersect ℓ₂ ℓ₁ :=
begin
  assume h,
  cases h with P hP,
  cases hP with h1 h2,
  have hl, from and.intro h2 h1,
  existsi P,
  assumption,
end

-- Show that if two lines are the same then they
-- intersect
lemma equal_intersect (ℓ₁ ℓ₂ : line) :
ℓ₁ = ℓ₂ → intersect ℓ₁ ℓ₂ :=
begin
  assume h,
  have h₂, from (line_eq ℓ₁ ℓ₂).mp h,
  have he, from (two_points ℓ₁),
  cases he with a ht,
  cases ht with b hab,

  existsi a,
  split,
    exact hab.right.left,
  exact (h₂ a) hab.right.left,
end
