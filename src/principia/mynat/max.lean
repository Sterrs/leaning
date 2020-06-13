import .nat_sub

namespace hidden

open mynat
-- TODO: generalise this to relevant types and relations
def max (a b : mynat) : mynat :=
if a ≤ b then b else a
def min (a b : mynat) : mynat :=
if a ≤ b then b else a

variables {a b c : mynat}

theorem le_imp_max2 (h : a ≤ b) : max a b = b := if_pos h

theorem le_imp_max1 (h : a ≤ b) : max b a = b :=
begin
  cases (le_iff_lt_or_eq.mp h) with hlt heq, {
    from if_neg hlt,
  }, {
    rw heq,
    from if_t_t _ _,
  },
end

@[simp]
theorem max_same : max a a = a := le_imp_max2 le_refl
@[simp]
theorem max_zero : max 0 a = a := le_imp_max2 zero_le
@[simp]
theorem max_succ : max a (succ a) = succ a := le_imp_max2 le_succ

theorem max_comm : max a b = max b a :=
by cases le_total_order a b; rw [le_imp_max1 h, le_imp_max2 h]

theorem max_le_left : a ≤ max a b :=
begin
  cases le_total_order a b,
    rwa le_imp_max2 h,
  rw [max_comm, le_imp_max2 h],
end

theorem max_le_right : b ≤ max a b :=
begin
  rw max_comm,
  from max_le_left,
end

theorem max_assoc : max a (max b c) = max (max a b) c :=
begin
  unfold max,
  by_cases hab: a ≤ b, {
    rw if_pos hab,
    by_cases hbc: b ≤ c, {
      rw if_pos hbc,
      rw if_pos (le_trans hab hbc),
    }, {
      rw if_neg hbc,
      rw if_pos hab,
    },
  }, {
    rw if_neg hab,
    by_cases hbc: b ≤ c, {
      rw if_pos hbc,
    }, {
      rw if_neg hbc,
      rw if_neg hab,
      rw if_neg (lt_trans hbc hab),
    },
  },
end

theorem max_lt_cancel_left : max a b < c → a < c :=
begin
  apply le_lt_chain,
  from max_le_left,
end

theorem max_lt_cancel_right : max a b < c → b < c :=
begin
  apply le_lt_chain,
  from max_le_right,
end

end hidden
