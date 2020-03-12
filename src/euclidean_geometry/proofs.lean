import .basic .incidence .order

-- Some proofs to get started

open classical

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
  exact hab.left,
  exact (h₂ a) hab.left,
end

-- Given a b intersect, if ℓ parallel to one it must
-- also intersect the other
lemma parallel_intersect {a b ℓ : line}
(distinct : a ≠ b)
(hpara : a ∥ ℓ) (h : intersect a b) :
intersect b ℓ :=
begin
  -- Consider case where a = ℓ separately
  cases hpara,

  rw ←hpara,
  symmetry,
  assumption,

  -- We want to form a contradiction to Euclid's axiom
  apply by_contradiction,
  assume hnb,
  cases h with P hP,
  -- Let's build the hypotheses we need for Euclid
  have ha : a ∥ ℓ, right, assumption,
  have hb: b ∥ ℓ, right, assumption,
  -- This one is unnecessarily complicated
  have hnP : ¬ P ⊏ ℓ,
    assume hPonℓ,
    have : intersect a ℓ,
    existsi P,
    split,
      from hP.left,
      assumption,
    contradiction,
  -- Now use Euclid's uniqueness to form contradiction
  have := euclid_unique hnP ⟨hP.left, ha⟩ ⟨hP.right, hb⟩,
  contradiction,
end

-- Transitivity of parallel
@[simp, trans]
theorem parallel_trans {ℓ₁ ℓ₂ ℓ₃ : line} (distinct : ℓ₁ ≠ ℓ₃):
ℓ₁ ∥ ℓ₂ → ℓ₂ ∥ ℓ₃ → ℓ₁ ∥ ℓ₃ :=
begin
  assume h12 h23,
  cases h12; cases h23,
  rw ←h23, left, assumption,
  rw h12, right, assumption,
  rw ←h23, right, assumption,
  -- The 'hard' case
  right,
  assume hi13,
  -- We need a parallel hypothesis back (ugly)
  have hpara : ℓ₁ ∥ ℓ₂, right, assumption,
  have := parallel_intersect distinct hpara hi13,
  have := intersect_symm this,
  contradiction,
end
