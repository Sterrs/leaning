import .le
import .mul

namespace hidden

namespace myrat

def lt (x y : myrat) := ¬y ≤ x

instance: has_lt myrat := ⟨lt⟩

instance decidable_lt: ∀ x y: myrat, decidable (x < y) :=
λ x y, not.decidable

variables x y z : myrat

theorem lt_iff_nle : x < y ↔ ¬y ≤ x := by refl

theorem zero_lt_mul (a b: myrat): 0 < a → 0 < b → 0 < a * b :=
begin
    assume hapos hbpos,
    sorry,
end

theorem lt_cancel_left {a b c : myrat} : c + a < c + b ↔ a < b := sorry

theorem lt_add_left {a b : myrat} (c : myrat) : a < b ↔ c + a < c + b :=
lt_cancel_left.symm

theorem lt_cancel_right {a b c : myrat} : a + c < b + c ↔ a < b :=
by rw [add_comm, add_comm b]; from lt_cancel_left

theorem lt_add_right {a b : myrat} (c : myrat) : a < b ↔ a + c < b + c :=
lt_cancel_right.symm

theorem lt_mul_pos_right {z : myrat} : 0 < z → ∀ x y : myrat, x < y ↔ x * z < y * z := sorry

theorem lt_mul_pos_left {z : myrat} : 0 < z → ∀ x y : myrat, x < y ↔ z * x < z * y := sorry

theorem lt_comb {a b c d: myrat}: a < b → c < d → a + c < b + d := sorry

-- It's debatable whether these should have b as an implicit or explicit
-- argument. When used like `transitivity`, by `apply`ing it, we need to supply
-- which middle term we are using.
-- However, in all other use cases we would supply both hypotheses.
-- Personally, I think `apply`ing these theorems should be the standard way to
-- use them as it involves the least `have` statements, resulting in shorter proofs
-- with fewer labels used (so no h, h₁, h₂, hxy, hxy₁ etc.)

theorem lt_le_chain {a c: myrat} (b : myrat): a < b → b ≤ c → a < c := sorry

theorem le_lt_chain {a c: myrat} (b : myrat): a ≤ b → b < c → a < c := sorry

theorem abs_lt (a b : myrat) : abs a < b ↔ -b < a ∧ a < b := sorry

theorem abs_lt_left {a b : myrat} : abs a < b → -b < a :=
λ h, by rw abs_lt at h; from h.left

theorem abs_lt_right {a b : myrat} : abs a < b → a < b :=
λ h, by rw abs_lt at h; from h.right

theorem lt_abs {a b : myrat} : a < abs b → b < -a ∨ a < b := sorry

-- abs_diff refers to the pattern `abs (a - b) < c` which often shows up in analysis

theorem abs_diff_lt_left {a b c : myrat} : abs (a - b) < c → b - c < a :=
begin
  assume h,
  have h₁ := abs_lt_left h,
  rwa [lt_add_right b, ←sub_add_neg, add_assoc, neg_self_add,
       add_zero, add_comm, sub_add_neg] at h₁,
end

theorem abs_diff_lt_right {a b c : myrat} : abs (a - b) < c → a < b + c :=
begin
  assume h,
  have h₁ := abs_lt_right h,
  rwa [lt_add_right b, ←sub_add_neg, add_assoc, neg_self_add,
       add_zero, add_comm] at h₁,
end

@[trans]
theorem lt_trans {a b c : myrat} : a < b → b < c → a < c := sorry

theorem zero_lt_one : (0 : myrat) < 1 :=
begin
  assume h,
  from one_nzero (le_antisymm h zero_le_one),
end

theorem zero_lt_two : (0 : myrat) < 2 :=
begin
  rw [←one_plus_one, ←zero_add (0 : myrat)],
  apply @lt_comb 0 1 0 1; from zero_lt_one,
end

theorem half_pos {ε : myrat} : 0 < ε → 0 < ε / 2 :=
assume h, by rwa [lt_mul_pos_right zero_lt_two, zero_mul, div_mul_cancel two_nzero]

theorem exists_between (a c : myrat) :
a < c → ∃ b : myrat, a < b ∧ b < c :=
begin
  assume hac,
  existsi (a + c) / 2,
  split; rw add_div, {
    rw [lt_add_left (-(a/2)), ←add_assoc, add_comm _ a, neg_self_add],
    conv {
      to_lhs,
      congr,
        rw ←@half_plus_half a, skip,
      skip,
    },
    rw [add_assoc, self_neg_add, add_zero, zero_add],
    rwa [lt_mul_pos_right zero_lt_two, div_mul_cancel two_nzero,
         div_mul_cancel two_nzero],
  }, {
    rw [lt_add_right (-(c / 2)), add_assoc, self_neg_add],
    conv {
      to_rhs,
      congr,
        rw ←@half_plus_half c, skip,
      skip,
    },
    rw [add_assoc, self_neg_add, add_zero, add_zero],
    rwa [lt_mul_pos_right zero_lt_two, div_mul_cancel two_nzero,
         div_mul_cancel two_nzero],
  },
end

theorem lt_mul_comb_nonneg {a b x y : myrat} : 0 ≤ a → 0 ≤ x → a < b → x < y → a * x < b * y := sorry

theorem lt_imp_ne {x y : myrat} : x < y → x ≠ y := sorry

theorem pos_iff_inv_pos : 0 < x ↔ 0 < x⁻¹ := sorry

end myrat

end hidden
