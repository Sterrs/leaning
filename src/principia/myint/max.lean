import .lt

namespace hidden

namespace myint

def max (a b : myint) : myint :=
if a ≤ b then b else a

def min (a b : myint) : myint :=
if a ≤ b then a else b

variables m n k : myint

@[simp]
theorem max_self : max m m = m :=
by apply if_pos; refl

-- Inconsistent with mynat/max.lean, I know
theorem le_imp_max {m n : myint} (hmn : m ≤ n): max m n = n :=
begin
  unfold max,
  rw if_pos hmn,
end

theorem le_imp_max_reverse {m n : myint} (hnm : n ≤ m) : max m n = m :=
begin
  by_cases m ≤ n, {
    rw [le_antisymm h hnm, max_self],
  }, {
    unfold max,
    rw if_neg h,
  },
end

theorem lt_imp_max {m n : myint} (hmn : m < n) : max m n = n :=
le_imp_max (lt_imp_le hmn)

theorem lt_imp_max_reverse {m n : myint} (hnm : n < m) : max m n = m :=
le_imp_max_reverse (lt_imp_le hnm)

theorem le_iff_max : m ≤ n ↔ max m n = n :=
begin
  split; assume h, {
    from le_imp_max h,
  }, {
    by_cases hmn : m ≤ n,
      assumption,
    rw ←lt_iff_nle at hmn,
    rw lt_imp_max_reverse hmn at h,
    exfalso,
    from lt_imp_ne hmn h.symm,
  },
end

theorem max_comm : max m n = max n m :=
begin
  by_cases m ≤ n,
    rw [le_imp_max h, le_imp_max_reverse h],
  rw ←lt_iff_nle at h,
  rw [lt_imp_max h, lt_imp_max_reverse h],
end

theorem le_iff_max_reverse : n ≤ m ↔ max m n = m :=
begin
  rw max_comm,
  from le_iff_max _ _,
end

-- This name is copied from mynat/max.lean, but it's not a great name
theorem le_max_right : n ≤ max m n :=
begin
  by_cases n ≤ m,
    have := (le_iff_max _ _).mp h,
    rw max_comm at this,
    rwa this,
  rw ←lt_iff_nle at h,
  rw lt_imp_max h,
end

theorem le_max_left : m ≤ max m n :=
by rw max_comm; from le_max_right _ _

instance : is_commutative myint max := ⟨max_comm⟩

-- Max distributes over itself
theorem max_max : max m (max n k) = max (max m n) (max m k) :=
begin
  unfold max,
  by_cases hmmxnk: m ≤ (max n k); unfold max at hmmxnk, {
    rw if_pos hmmxnk,
    by_cases hnk: n ≤ k, {
      rw if_pos hnk,
      rw if_pos hnk at hmmxnk,
      repeat {rw if_pos hmmxnk},
      by_cases hmn: m ≤ n, {
        repeat {rw if_pos hmn},
        rw if_pos hnk,
      }, {
        repeat {rw if_neg hmn},
        rw if_pos hmmxnk,
      },
    }, {
      rw if_neg hnk,
      rw if_neg hnk at hmmxnk,
      repeat {rw if_pos hmmxnk},
      by_cases hmk: m ≤ k, {
        repeat {rw if_pos hmk},
        rw if_neg hnk,
      }, {
        repeat {rw if_neg hmk},
        have := max_comm,
        unfold max at this,
        rw this,
        rw if_pos hmmxnk,
      },
    },
  }, {
    rw if_neg hmmxnk,
    have hmk: ¬m ≤ k, {
      assume hmk,
      have := le_trans _ hmk (le_max_right n k),
      from hmmxnk this,
    },
    have hmn: ¬m ≤ n, {
      assume hmk,
      have := le_trans _ hmk (le_max_left n k),
      from hmmxnk this,
    },
    repeat {rw if_neg hmk <|> rw if_neg hmn},
    rw if_pos (le_refl _),
  },
end

theorem max_assoc : max (max m n) k = max m (max n k) :=
begin
  by_cases m ≤ n,
    rw le_imp_max h,
    have : m ≤ max n k,
      transitivity n,
        assumption,
      from le_max_left _ _,
    rw le_imp_max this,
  sorry,
end

instance : is_associative myint max := ⟨max_assoc⟩

theorem max_eq_either : max m n = m ∨ max m n = n :=
begin
  by_cases m ≤ n,
    right, rwa le_imp_max,
  left,
  rw ←lt_iff_nle at h,
  rwa lt_imp_max_reverse,
end

-- Just casework?
theorem max_sum_le (a b c d : myint) : max (a + c) (b + d) ≤ max a b + max c d := sorry

theorem nonneg_mul_max {m : myint}:
0 ≤ m → ∀ n k, m * max n k = max (m * n) (m * k) := sorry

def abs : myint → myint := λ m, max m (-m)

theorem abs_eq_max : abs m = max m (-m) := rfl

theorem abs_neg: abs (-n) = abs n :=
by rw [abs_eq_max, max_comm, neg_neg, ←abs_eq_max]

theorem abs_of_nonneg {m : myint} (h : 0 ≤ m): abs m = m :=
begin
  rw [abs_eq_max, max_comm, ←le_iff_max],
  transitivity (0 : myint),
  rwa [le_add_right (-m), zero_add, self_neg_add] at h,
  assumption,
end

theorem abs_nonneg : 0 ≤ abs m :=
begin
  by_cases 0 ≤ m,
    rwa abs_of_nonneg h,
  rw [←lt_iff_nle, lt_add_right (-m), self_neg_add, zero_add] at h,
  rw [←abs_neg, abs_of_nonneg (lt_imp_le h)],
  from lt_imp_le h,
end

theorem zero_le_abs: 0 ≤ m → m = abs m :=
begin
  assume h0m,
  unfold abs, unfold max,
  by_cases hmm: m ≤ -m, {
    rw if_pos hmm,
    have: -m ≤ 0, {
      rw le_add_left m,
      simp,
      assumption,
    },
    repeat {rw ←le_antisymm h0m (le_trans _ hmm this)},
    refl,
  }, {
    rw if_neg hmm,
  },
end

theorem zero_lt_abs: 0 < m → m = abs m :=
begin
  assume h,
  apply zero_le_abs,
  apply lt_imp_le,
  assumption,
end

private theorem abs_cancel_abs_mul_within : abs (abs m * n) = abs (m * n) :=
begin
  unfold abs,
  by_cases -m ≤ m,
    rw le_imp_max_reverse h,
  rw ←lt_iff_nle at h,
  rw [lt_imp_max h, max_comm, mul_neg_with, neg_neg],
end

-- Short lemma above avoids any casework
theorem abs_mul: abs (m * n) = abs m * abs n :=
begin
  have : abs m * abs n = abs (abs m * abs n),
    have : 0 ≤ abs m * abs n,
      rw ←zero_mul 0,
      apply le_mul_comb_nonneg, any_goals { refl },
        from abs_nonneg _,
        from abs_nonneg _,
      rw abs_of_nonneg this,
  rw this,
  rw [abs_cancel_abs_mul_within, mul_comm m (abs n), abs_cancel_abs_mul_within, mul_comm],
end

-- The following three theorems are practically equivalent, needs reorganising a bit
theorem abs_nonneg_mul {m : myint} : 0 ≤ m → ∀ n, m * abs n = abs (m * n) :=
begin
  assume h0m,
  intro n,
  conv {
    to_lhs,
    congr,
    rw zero_le_abs _ h0m,
  },
  rw abs_mul,
end

theorem abs_le_square: abs m ≤ abs n ↔ m * m ≤ n * n :=
begin
  split; assume h, {
    have := le_mul_comb_nonneg (abs_nonneg _) (abs_nonneg _) h h,
    rw [←abs_mul, ←abs_mul] at this,
    rwa [abs_of_nonneg (square_nonneg m), abs_of_nonneg (square_nonneg n)] at this,
  }, {
    rw [←abs_of_nonneg (square_nonneg m), ←abs_of_nonneg (square_nonneg n)] at h,
    rwa [abs_mul, abs_mul, ←le_sqrt_nonneg (abs_nonneg _) (abs_nonneg _)] at h,
  },
end

theorem le_self_abs: m ≤ abs m :=
begin
  unfold abs,
  from le_max_left _ _,
end

-- At least it makes this easy :P
theorem triangle_ineq: abs (m + n) ≤ abs m + abs n :=
begin
  repeat { rw abs_eq_max, },
  rw neg_distr,
  from max_sum_le _ _ _ _,
end

theorem zero_iff_abs_zero: m = 0 ↔ abs m = 0 :=
begin
  split, {
    assume hm0,
    rw hm0,
    refl,
  }, {
    assume habs,
    unfold abs at habs,
    unfold max at habs,
    by_cases hmm: (m ≤ -m), {
      rw if_pos hmm at habs,
      rw ←add_cancel (-m),
      simp,
      symmetry,
      assumption,
    }, {
      rw if_neg hmm at habs,
      assumption,
    },
  },
end

theorem sign_mul_self_abs: m * sign m = abs m :=
begin
  by_cases h0m: 0 < m, {
    rw pos_sign _ h0m,
    rw mul_one,
    from zero_lt_abs _ h0m,
  }, {
    by_cases hm0: m < 0, {
      rw neg_sign _ hm0,
      rw mul_neg,
      rw mul_one,
      rw lt_add_right (-m) at hm0,
      simp at hm0,
      rw ←abs_neg,
      from zero_lt_abs _ hm0,
    }, {
      cases lt_trichotomy 0 m, {
        rw ←h,
        refl,
      }, {
        cases h; contradiction,
      },
    },
  },
end


theorem zero_lt_sign_mul_self: m ≠ 0 → 0 < m * sign m :=
begin
  assume hmn0,
  rw sign_mul_self_abs,
  rw lt_iff_le_and_ne,
  split, {
    from abs_nonneg _,
  }, {
    assume h,
    have := (zero_iff_abs_zero _).mpr h.symm,
    contradiction,
  },
end

end myint

end hidden
