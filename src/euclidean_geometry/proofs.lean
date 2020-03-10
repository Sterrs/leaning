import .basic .incidence .order

-- Read disclaimer in basic.lean

-- Some proofs to get started

open classical

-- Prove the existence of a point
-- I don't know if we can actually get the point
theorem there_is_a_point : ∃ (a : point), true :=
begin
  cases noncoll3 with a ha,
  constructor,
  assumption,
  exact true.intro,
end

-- Show that the intersect relation is symmetric
theorem intersect_symm {ℓ₁ ℓ₂ : line} :
intersect ℓ₁ ℓ₂ → intersect ℓ₂ ℓ₁ :=
begin
  assume h,
  cases h with p hp,
  cases hp with h1 h2,
  have hl, from and.intro h2 h1,
  existsi p,
  assumption,
end

-- Show that the parallel relation is symmetric
theorem parallel_symm {ℓ₁ ℓ₂ : line} :
parallel ℓ₁ ℓ₂ → parallel ℓ₂ ℓ₁ :=
begin
  assume h hi21,
  have hi12, from intersect_symm hi21,
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

-- Equal lines are not parallel
lemma eq_not_parallel {ℓ₁ ℓ₂ : line} :
ℓ₁ = ℓ₂ → ¬ parallel ℓ₁ ℓ₂ :=
begin
  assume h hpara,
  have hinter, from (equal_intersect ℓ₁ ℓ₂) h,
  contradiction,
end

-- Parallel lines are not equal
lemma para_not_eq {ℓ₁ ℓ₂ : line} :
parallel ℓ₁ ℓ₂ → ℓ₁ ≠ ℓ₂ :=
begin
  -- Is there a more straightforward way to
  -- get this from the previous lemma?
  assume hpara heq,
  have h, from eq_not_parallel heq,
  contradiction,
end

#check euclid_unique
-- Given ℓ₁ ℓ₂ intersect, if l parallel to one it must
-- also intersect the other
lemma parallel_intersect {ℓ₁ ℓ₂ l : line}
(distinct : ℓ₁ ≠ ℓ₂)
(hpara : parallel ℓ₁ l) (h : intersect ℓ₁ ℓ₂) :
intersect ℓ₂ l :=
begin
  cases h with p hp,
  apply classical.by_contradiction,
  assume hni,
  have : ℓ₁ = ℓ₂,
  have pnl : ¬ lies_on p l,
  assume hpnl : lies_on p l,
  have hℓ₁l: intersect ℓ₁ l,
  existsi p,
  exact ⟨hp.left, hpnl⟩,
  contradiction,

  apply euclid_unique ℓ₁ ℓ₂ l p,
  assumption,
  exact ⟨hp.left, hpara⟩,
  exact ⟨hp.right, hni⟩,

  contradiction,
end

-- Transitivity of parallel
theorem parallel_trans {ℓ₁ ℓ₂ ℓ₃ : line} (distinct : ℓ₁ ≠ ℓ₃):
parallel ℓ₁ ℓ₂ → parallel ℓ₂ ℓ₃ → parallel ℓ₁ ℓ₃ :=
begin
  assume h12 h23,
  assume hi13,
  have hneq23, from para_not_eq h23,
  have hneq12, from para_not_eq h12,
  have h₁,
  from parallel_intersect distinct h12 hi13,
  have h₂, from intersect_symm h₁,
  contradiction,
end
