import ..logic
import .le

namespace hidden
namespace quotint

open quotint

variables m n k : quotint
variables a b c : mynat

-- this is no longer definitionally true. Not sure if that's what we want,
-- it makes things a bit ugly
theorem lt_iff_nle : m < n ↔ ¬n ≤ m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  refl,
end

instance decidable_lt: ∀ m n: quotint, decidable (m < n) :=
quotient_decidable_rel int_pair.lt int_pair.lt_well_defined

theorem lt_nrefl : ¬m < m :=
begin
  assume h,
  rw lt_iff_nle at h,
  from h (le_refl m),
end

theorem lt_imp_ne {m n : quotint}: m < n → m ≠ n :=
begin
  assume hlt heq, subst heq,
  from lt_nrefl m hlt,
end

theorem lt_imp_le {m n : quotint}: m < n → m ≤ n :=
begin
  assume hmn,
  cases @le_total_order m n,
    assumption,
  exfalso,
  rw lt_iff_nle at hmn,
  contradiction,
end

theorem lt_iff_le_and_ne : m < n ↔ m ≤ n ∧ m ≠ n :=
begin
  split; assume h, {
    cases @le_total_order m n with hmn hnm,
      split, assumption,
      from lt_imp_ne h,
    have hmn := lt_imp_le h, exfalso,
    from (lt_imp_ne h) (le_antisymm hmn hnm),
  }, {
    rw lt_iff_nle,
    assume hmn,
    cases h with hnm hne,
    from hne (le_antisymm hnm hmn),
  },
end

@[simp]
theorem lt_cancel {m n k : quotint} : m + k < n + k ↔ m < n :=
begin
  split; assume h,
  all_goals {
    rw lt_iff_le_and_ne at *,
    simp at *,
    assumption,
  },
end

theorem lt_add {m n : quotint} (k : quotint): m < n ↔ m + k < n + k :=
⟨lt_cancel.mpr, lt_cancel.mp⟩

theorem lt_add_left {m n : quotint} (k : quotint) : m < n ↔ k + m < k + n :=
begin
  rw [add_comm, @add_comm k],
  symmetry,
  exact lt_cancel,
end

@[simp]
theorem lt_cancel_left {m n k : quotint} : k + m < k + n ↔ m < n :=
⟨(lt_add_left k).mpr, (lt_add_left k).mp⟩

theorem pos_add {m n : quotint} : 0 < m → 0 < n → 0 < m + n :=
begin
  assume hm hn,
  rw lt_iff_le_and_ne at *,
  cases hm with hm hmne0,
  cases hn with hn hnne0,
  split, {
    from le_comb hm hn,
  }, {
    assume h,
    have : m = -n,
      rw [←add_cancel n, neg_self_add],
      from h.symm,
    subst this,
    rw le_neg_switch at hm,
    simp at hm,
    from hnne0 (le_antisymm hn hm),
  },
end

theorem lt_iff_sub_pos: m < n ↔ 0 < n + -m :=
begin
  split; assume h, {
    rw lt_add (-m) at h,
    simp at h, assumption,
  }, {
    rw [lt_add m, add_assoc] at h,
    simp at h, assumption,
  },
end

theorem lt_comb {m n k j : quotint} : m < n → k < j → m + k < n + j :=
begin
  assume hmn hkj,
  rw lt_iff_sub_pos at *,
  have h := pos_add hmn hkj,
  have : n + -m + (j + -k) = n + j + -(m + k),
    simp,
    ac_refl,
  rwa this at h,
end

@[trans]
theorem lt_trans : m < n → n < k → m < k :=
begin
  assume hmn hnk,
  have h := lt_comb hmn hnk,
  rw add_comm at h,
  simp at h,
  assumption,
end

theorem lt_mul_comb_nonneg {m n a b : quotint}
(hm : 0 ≤ m) (ha : 0 ≤ a) (hmn : m < n) (hab : a < b) :
m * a < n * b :=
begin
  sorry,
end

-- For myrat
theorem zero_lt_mul : 0 < m → 0 < n → 0 < m * n :=
begin
  assume hm hn,
  rw ←zero_mul 0,
  apply lt_mul_comb_nonneg; refl <|> assumption, -- Yes, I watch Rick and Morty
end

theorem zero_lt_one : 0 < (1 : quotint) :=
begin
  sorry,
end

theorem zero_le_one : 0 ≤ (1 : quotint) :=
lt_imp_le zero_lt_one

theorem le_mul_cancel_pos_left : 0 < k → (k * m ≤ k * n ↔ m ≤ n) := sorry

theorem le_mul_cancel_pos_right : 0 < k → (m * k ≤ n * k ↔ m ≤ n) := sorry

theorem zero_lt_sign_mul_self: m ≠ 0 → 0 < (sign m) * m := sorry

end quotint
end hidden
