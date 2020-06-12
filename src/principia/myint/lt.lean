import ..logic
import .le

namespace hidden
namespace myint

open myint

def lt (m n : myint): Prop := ¬n ≤ m
instance: has_lt myint := ⟨lt⟩

variables {m n k : myint}
variables {a b c : mynat}

theorem lt_iff_nle : m < n ↔ ¬n ≤ m :=
by split; all_goals { assume h, assumption }

instance decidable_lt: ∀ m n: myint, decidable (m < n) :=
(λ m n, not.decidable)

theorem nat_nat_lt : (↑a : myint) < ↑b ↔ a < b :=
iff_to_contrapositive nat_nat_le

theorem nat_neg_lt : ¬↑a < -[1+ b] :=
assume h, h neg_nat_le

theorem neg_nat_lt : -[1+ a] < ↑b :=
assume h, nat_neg_le h

theorem neg_net_lt : -[1+ a] < -[1+ b] ↔ b < a :=
iff_to_contrapositive neg_neg_le

theorem lt_nrefl : ¬m < m := assume h, h le_refl

theorem lt_imp_ne : m < n → m ≠ n :=
begin
  assume hlt heq, subst heq,
  from lt_nrefl hlt,
end

theorem lt_imp_le : m < n → m ≤ n := sorry

@[trans]
theorem lt_trans : m < n → n < k → m < k :=
begin
  assume hmn hnk hkm,
  rw le_iff_exists_nat at hkm,
  cases hkm with a ha,
  subst ha,
  rw [lt_iff_nle, le_iff_exists_nat] at hnk,
  sorry,
end

-- For myrat
theorem zero_lt_mul : 0 < m → 0 < n → 0 < m * n :=
begin
  assume h0m h0n,
  have h0lem := lt_imp_le h0m,
  have h0len := lt_imp_le h0n,
  rw zero_le_iff_coe at h0lem h0len,
  cases h0lem with a ha,
  cases h0len with b hb,
  subst ha, subst hb,
  rw [←zero_nat, nat_nat_lt] at h0m h0n,
  rw [←zero_nat, nat_nat_mul, nat_nat_lt],
  have := lt_comb_mul h0n h0m,
  rwa [hidden.mul_zero, hidden.mul_comm] at this,
end

theorem zero_le_one : 0 < (1 : myint) :=
begin
  assume h,
  rw le_iff_exists_nat at h,
  cases h with a h,
  rw [←zero_nat, ←one_nat, nat_nat_add, of_nat_cancel] at h,
  from mynat.no_confusion (add_integral h.symm),
end

theorem zero_lt_sign_mul_self: m ≠ 0 → 0 < (sign m) * m := sorry

theorem zero_lt_abs: 0 < m → m = ↑(abs m) := sorry

-- needed for rationals
theorem le_mul_cancel_pos: 0 < k → m * k ≤ n * k → m ≤ n := sorry

end myint
end hidden
