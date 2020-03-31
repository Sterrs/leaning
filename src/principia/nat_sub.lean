import principia.mynat
import principia.le
import principia.lt
import principia.logic

namespace hidden

open mynat

variables m n k: mynat

-- Subtraction

def sub: mynat → mynat → mynat
| m 0               := m
| 0 n               := 0
| (succ m) (succ n) := sub m n

instance: has_sub mynat := ⟨sub⟩

@[simp] theorem sub_succ_succ : succ m - succ n = m - n := rfl

-- Reverse implication does NOT hold
-- Is there any point having this as a theorem
theorem sub_congr: m = n → m - k = n - k :=
begin
  assume h,
  congr,
  assumption,
end

-- °_° why doesn't this work the normal way
@[simp]
theorem sub_zero: m - 0 = m :=
begin
  cases m,
    refl,
  refl,
end

@[simp]
theorem zero_sub: 0 - m = 0 :=
begin
  cases m,
    refl,
  refl,
end

@[simp]
theorem sub_self_eq_zero: n - n = 0 :=
begin
  induction n with n hn,
    refl,
  rwa sub_succ_succ,
end

@[simp]
theorem succ_sub_self: (succ m) - m = 1 :=
begin
  induction m with m hm,
    simp,
  rwa sub_succ_succ,
end

-- Watch out, similar things do not hold, e.g. (5 - 6) + 6 ≠ 5
@[simp]
theorem add_sub: (m + n) - n = m :=
begin
  induction n with n hn,
    rw [zz, add_zero, sub_zero],
  rwa [add_succ, sub_succ_succ],
end
-- Simple corollaries of the above
@[simp] theorem add_sub_one: (m + 1) - 1 = m := add_sub m 1
@[simp]
theorem succ_sub_one: (succ m) - 1 = m := by rwa [←add_one_succ, add_sub]

theorem sub_zero_iff_le: m - n = 0 ↔ m ≤ n :=
begin
  cases le_total_order m n with hmn hnm, {
    split, {
      cc,
    }, {
      assume hmn2,
      cases hmn with d hd,
      rw hd,
      induction m with m_n m_ih generalizing n, {
        simp,
      }, {
        rw [succ_add, sub_succ_succ],
        cases n, {
          exfalso,
          from succ_ne_zero _ (add_integral _ _ hd.symm),
        }, {
          apply m_ih n (le_succ_cancel _ _ hmn2),
          apply succ_inj,
          rwa succ_add at hd,
        },
      },
    },
  }, {
    split, {
      assume hmn,
      cases hnm with d hd,
      rw [hd, add_comm, add_sub] at hmn,
      rw hmn at hd,
      rw [hd, add_zero],
      from le_refl _,
    }, {
      assume hmn,
      have hmeqn := le_antisymm _ _ hnm hmn,
      rw hmeqn,
      from sub_self_eq_zero _,
    }
  }
end

-- just the contrapositive. Useful later
theorem sub_nzero_iff_gt: m - n ≠ 0 ↔ n < m :=
begin
  from iff_to_contrapositive _ _ (sub_zero_iff_le m n),
end

theorem sub_succ_impl_le: m - n = succ k → n < m :=
begin
  assume hmnsk,
  rw ←sub_nzero_iff_gt,
  rw hmnsk,
  from succ_ne_zero _,
end

theorem sub_succ_rearrange: m - n = succ k ↔ m = succ k + n :=
begin
  split, {
    assume hmnsk,
    have hnlm := sub_succ_impl_le _ _ _ hmnsk,
    rw lt_iff_succ_le at hnlm,
    cases hnlm with d hd,
    rw [hd, add_comm, add_succ, ←succ_add, add_sub] at hmnsk,
    rw [hd, ←hmnsk, succ_add, succ_add, add_comm],
  }, {
    assume hmskn,
    rw [hmskn, add_sub],
  },
end

theorem sub_succ_cancel: succ m - n = succ k → m - n = k :=
begin
  rw [sub_succ_rearrange, succ_add],
  assume hmkn,
  rw [succ_inj _ _ hmkn, add_sub],
end

theorem sub_overkill: m - (m + k) = 0 :=
begin
  rw sub_zero_iff_le,
  from le_to_add m k,
end

theorem sub_le: m - n ≤ m :=
begin
  cases hmn: m - n, {
    from zero_le _,
  }, {
    rw sub_succ_rearrange at hmn,
    existsi n,
    assumption,
  }
end

theorem sub_from_le: m ≤ n → m - k ≤ n :=
begin
  assume hmn,
  cases (sub_le m k) with d1 hd1,
  cases hmn with d2 hd2,
  existsi d1 + d2,
  rw hd2,
  conv {
    to_lhs,
    rw hd1,
  },
  rwa add_assoc,
end

@[simp]
theorem sub_switch_one: (m - n) - 1 = (m - 1) - n :=
begin
  cases h: (m - n) - 1, {
    symmetry,
    rw [zz, sub_zero_iff_le],
    rw [zz, sub_zero_iff_le] at h,
    cases h with d hd,
    cases d, {
      simp at hd,
      have hr := (sub_succ_rearrange _ _ _).mp hd.symm,
      have : succ 0 = 1 := rfl,
      rw [hr, add_comm, zz, this, add_sub n 1],
      from le_refl _,
    }, {
      have hmn0 := add_integral _ _ (succ_inj _ _ hd.symm),
      rw sub_zero_iff_le at hmn0,
      from sub_from_le _ _ _ hmn0,
    },
  }, {
    symmetry,
    rw [sub_succ_rearrange, succ_add, sub_succ_rearrange],
    rw [sub_succ_rearrange, succ_add, sub_succ_rearrange] at h,
    rw h,
    simp,
  },
end

@[simp]
theorem sub_succ: m - (succ n) = m - n - 1 :=
begin
  induction m with m hm,
    repeat { rw zz <|> rw zero_sub },
  rw [sub_succ_succ, ←add_one_succ, sub_switch_one, add_sub_one],
end

@[simp]
theorem sub_distr: m - (n + k) = m - n - k :=
begin
  induction k with k hk,
    rw [zz, add_zero, sub_zero],
  rw [sub_succ, ←hk, ←sub_succ, add_succ],
end

@[simp]
theorem sub_switch: (m - n) - k = (m - k) - n :=
begin
  induction k with k hk,
    repeat { rw zz <|> rw sub_zero },
  repeat { rw sub_succ },
  rw [←sub_switch_one (m - k), hk],
end

@[simp] theorem mul_sub: m * (n - k) = m * n - m * k :=
begin
  induction m with m hm, {
    simp,
  }, {
    cases hmnk: succ m * (n - k), {
      symmetry,
      rw [zz, sub_zero_iff_le],
      apply le_mul,
      rw ←sub_zero_iff_le,
      from mul_integral _ _ (succ_ne_zero _) hmnk,
    }, {
      cases hnk: n - k, {
        rw hnk at hmnk,
        simp at hmnk,
        exfalso, from succ_ne_zero _ hmnk.symm,
      },
      symmetry,
      rw sub_succ_rearrange,
      rw sub_succ_rearrange at hnk,
      rw [hnk, add_sub] at hmnk,
      rw [←hmnk, hnk],
      rw mul_add,
    },
  },
end

@[simp] theorem sub_mul: (m - n) * k = m * k - n * k :=
by rw [mul_comm, mul_comm m, mul_comm n k, mul_sub]
-- Cute corollary
@[simp]
theorem difference_two_squares: m * m - n * n = (m - n) * (m + n) :=
by rw [sub_mul, mul_add, mul_add, sub_distr, mul_comm m n, add_sub]

end hidden
