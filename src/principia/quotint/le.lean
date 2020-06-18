import .basic
import .int_pair
import .mul

import ..mynat.sum

namespace hidden

namespace quotint

open mynat

variables m n k x y z : quotint
variables a b c : mynat

@[simp]
theorem nat_nat_le: (↑a:quotint) ≤ ↑b ↔ a ≤ b := iff.rfl

@[simp]
theorem nat_neg_le: ¬(↑a ≤ -[1+ b]) :=
mynat.succ_nle_zero

@[simp]
theorem neg_nat_le: -[1+ a] ≤ ↑b :=
mynat.zero_le

@[simp]
theorem neg_neg_le: -[1+ a] ≤ -[1+ b] ↔ b ≤ a :=
begin
  repeat {rw neg_succ_def},
  rw le_eq_cls rfl rfl,
  simp,
  from iff.intro mynat.le_succ_cancel (mynat.le_add 1),
end

instance decidable_le: ∀ m n : quotint, decidable (m ≤ n) :=
quotient_decidable_rel int_pair.le int_pair.le_well_defined

@[refl]
theorem le_refl: m ≤ m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  from mynat.le_refl,
end

-- Forward implication of definitions being equal
private theorem le_iff_exists_nat_mpr {m n : quotint}:
m ≤ n → ∃ c : mynat, n = m + ↑c :=
begin
  assume hmn,
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  rw le_eq_cls rfl rfl at hmn,
  cases hmn with d hd,
  existsi d,
  rw coe_nat_def,
  rw add_eq_cls rfl rfl,
  apply quotient.sound,
  rw int_pair.setoid_equiv,
  simp,
  rw hd,
  ac_refl,
end

lemma le_add_rhs_coe {m n : quotint}: m ≤ n → m ≤ n + ↑c :=
begin
  assume hmn,
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  rw coe_nat_def,
  rw add_eq_cls rfl rfl,
  rw le_eq_cls rfl rfl,
  rw le_eq_cls rfl rfl at hmn,
  rw int_pair.le_def at *,
  simp,
  have: b.a + c + a.b = b.a + a.b + c := by ac_refl,
  rw this,
  from mynat.le_add_rhs hmn,
end

-- Show old defn of ≤ is equivalent (very useful)
theorem le_iff_exists_nat: m ≤ n ↔ ∃ a : mynat, n = m + ↑a :=
begin
  split, {
    from le_iff_exists_nat_mpr,
  }, {
    assume h,
    cases h with a ha,
    subst ha,
    apply le_add_rhs_coe,
    refl,
  },
end

@[trans]
theorem le_trans {m k : quotint} (n : quotint) : m ≤ n → n ≤ k → m ≤ k :=
begin
  assume hmn hnk,
  rw le_iff_exists_nat at hmn,
  cases hmn with a ha,
  rw le_iff_exists_nat at hnk,
  cases hnk with b hb,
  rw [ha, add_assoc, nat_nat_add] at hb,
  rw le_iff_exists_nat,
  existsi (a+b),
  assumption,
end

@[simp]
theorem le_cancel_right {m n k : quotint}: m + k ≤ n + k ↔ m ≤ n :=
begin
  split; assume h, {
    rw le_iff_exists_nat at h,
    cases h with a h,
    rw [add_assoc, @add_comm k, ←add_assoc, add_cancel] at h,
    rw le_iff_exists_nat,
    existsi a,
    assumption,
  }, {
    rw le_iff_exists_nat at h,
    cases h with a h,
    rw [h, add_assoc, @add_comm ↑a, ←add_assoc, le_iff_exists_nat],
    existsi a,
    refl,
  },
end

theorem le_add_right {m n : quotint} (k  : quotint): m ≤ n ↔ m + k ≤ n + k :=
le_cancel_right.symm

@[simp]
theorem le_cancel_left {m n k : quotint}: k + m ≤ k + n ↔ m ≤ n :=
begin
  rw [quotint.add_comm, @quotint.add_comm k],
  simp,
end

theorem le_add_left {m n : quotint} (k : quotint) : m ≤ n ↔ k + m ≤ k + n :=
le_cancel_left.symm

@[simp]
theorem le_cancel_to_zero_lhs: m ≤ m + n ↔ 0 ≤ n :=
by rw [←@zero_add m, add_assoc, @add_comm m, ←add_assoc,
       le_cancel_right, zero_add]

-- Exact same proof works :o
@[simp]
theorem le_cancel_to_zero_rhs: m + n ≤ m ↔ n ≤ 0 :=
by rw [←@zero_add m, add_assoc, @add_comm m, ←add_assoc,
       le_cancel_right, zero_add]

theorem le_neg_switch: m ≤ n ↔ -n ≤ -m :=
begin
  rw @le_add_right (-n) (-m) (n + m),
  conv in (-m + (n + m)) {
    congr, skip,
    rw add_comm,
  },
  repeat {rw ←add_assoc},
  repeat {rw neg_self_add},
  simp,
end

theorem zero_le_iff_coe: 0 ≤ m ↔ ∃ a: mynat, m = ↑a :=
begin
  split; assume h, {
    rw le_iff_exists_nat at h,
    cases h with a h,
    rw zero_add at h,
    existsi a,
    assumption,
  }, {
    rw le_iff_exists_nat,
    cases h with a h,
    existsi a,
    rwa zero_add,
  },
end

theorem le_zero_iff_neg_coe: m ≤ 0 ↔ ∃ a : mynat, m = -↑a :=
begin
  split; assume h, {
    rw le_iff_exists_nat at h,
    cases h with a h,
    rw [←add_cancel (-↑a), add_assoc, self_neg_add, zero_add,
    add_zero] at h,
    existsi a,
    symmetry, assumption,
  }, {
    cases h with a h,
    rw le_iff_exists_nat,
    existsi a,
    rw [←add_cancel (-↑a), add_assoc, self_neg_add, zero_add,
    add_zero],
    symmetry, assumption,
  },
end

theorem le_comb {m n x y : quotint}: m ≤ n → x ≤ y → m + x ≤ n + y :=
begin
  assume hmn hxy,
  rw [le_add_right x, @add_comm n] at hmn,
  rw [le_add_right n, @add_comm y] at hxy,
  transitivity (x + n); assumption,
end

theorem le_total_order (m n : quotint): m ≤ n ∨ n ≤ m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  from mynat.le_total_order _ _,
end

theorem le_mul_nonneg_left {m n k : quotint}: 0 ≤ k → m ≤ n → k * m ≤ k * n :=
begin
  assume h0lek hmn,
  rw zero_le_iff_coe at h0lek,
  cases h0lek with a ha,
  rw le_iff_exists_nat at hmn,
  cases hmn with b hb,
  rw [ha, hb, mul_add, le_cancel_to_zero_lhs, nat_nat_mul],
  rw zero_le_iff_coe,
  existsi (a*b),
  refl,
end

theorem le_mul_nonneg_right {m n k : quotint}: 0 ≤ k → m ≤ n → m * k ≤ n * k :=
λ hk hmn, by rw [mul_comm, mul_comm n]; from le_mul_nonneg_left hk hmn

theorem le_mul_nonpos_left {m n k : quotint}: k ≤ 0 → m ≤ n → k * n ≤ k * m :=
begin
  assume hkle0 hmn,
  rw le_zero_iff_neg_coe at hkle0,
  cases hkle0 with a ha,
  rw [ha, neg_mul, neg_mul, le_neg_switch, neg_neg, neg_neg],
  have : 0 ≤ (↑a : quotint), {
    rw zero_le_iff_coe,
    existsi a,
    refl,
  },
  from le_mul_nonneg_left this hmn,
end

theorem le_antisymm {m n : quotint}: m ≤ n → n ≤ m → m = n :=
begin
  assume hmn hnm,
  rw le_iff_exists_nat at hmn hnm,
  cases hmn with a ha,
  cases hnm with b hb,
  have hb₁ := hb.symm,
  rw [ha, add_assoc, add_comm, add_cancel_to_zero, nat_nat_add,
      ←zero_nat, of_nat_cancel] at hb₁,
  have := add_integral hb₁,
  rw [this, zero_nat, add_zero] at ha,
  symmetry,
  assumption,
end

theorem square_nonneg: 0 ≤ m * m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw mul_eq_cls rfl rfl,
  rw int_zero,
  rw le_eq_cls rfl rfl,
  rw int_pair.le_def,
  simp,
  have: a.a * a.b + a.b * a.a = 2 * (a.a * a.b), {
    have: (2: mynat) = 1 + 1 := rfl,
    rw this,
    simp,
    ac_refl,
  },
  rw this,
  from mynat.am_gm_2 _ _,
end

-- is this somewhere else?
theorem coe_inj {m n: mynat}: (↑m: quotint) = ↑n → m = n :=
begin
  sorry,
end

theorem le_mul_comb_nonneg {m n a b : quotint} (hm : 0 ≤ m) (ha : 0 ≤ a)
(hmn : m ≤ n) (hab : a ≤ b) : m * a ≤ n * b :=
begin
  transitivity (n * a),
    apply le_mul_nonneg_right; assumption,
  apply le_mul_nonneg_left,
    transitivity m; assumption,
  assumption,
end

end quotint
end hidden
