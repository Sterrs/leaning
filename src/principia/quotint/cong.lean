import .dvd
import .mul

namespace hidden
open quotint

-- a and b are congruent modulo n
def cong (n a b : quotint) : Prop := ∃ k : quotint, a = b + n * k

-- Throughout this section we will work modulo n
section mod_n

-- Fix a value n, which we will work modulo
parameter {n : quotint}
-- Write ≅ for congruent modulo n
local infix `≅`:50 := cong n

variables {a b c x y z : quotint}

@[refl]
theorem cong_refl : a ≅ a :=
begin
  existsi (0 : quotint),
  rw [quotint.mul_zero, quotint.add_zero],
end

@[symm]
theorem cong_symm : a ≅ b → b ≅ a :=
begin
  assume h,
  cases h with k hk,
  existsi -k,
  rw mul_neg,
  rw ←(@quotint.add_cancel _ _ (n * k)),
  rw [quotint.add_assoc, quotint.neg_self_add, quotint.add_zero],
  symmetry,
  assumption,
end

@[trans]
theorem cong_trans : a ≅ b → b ≅ c → a ≅ c :=
begin
  assume hab hbc,
  cases hab with k hk,
  cases hbc with m hm,
  rw [hm, quotint.add_assoc, ←quotint.mul_add] at hk,
  existsi m + k,
  assumption,
end

theorem cong_self_to_zero : n ≅ 0 :=
begin
  existsi (1:quotint),
  rw [quotint.zero_add, quotint.mul_one],
end

theorem cong_add_same : a ≅ b → a + c ≅ b + c :=
begin
  assume h,
  cases h with k hk,
  unfold cong,
  rw hk,
  existsi k,
  -- Basic arithmetic
  sorry,
end

theorem cong_add : a ≅ b → x ≅ y → a + x ≅ b + y :=
begin
  sorry,
end

theorem cong_mul_same : a ≅ b → c * a ≅ c * b := sorry

theorem cong_mul : a ≅ b → x ≅ y → a * x ≅ b * y := sorry


theorem cong_zero_iff_dvd : a ≅ 0 ↔ n ∣ a := sorry

-- Euclid's Lemma
theorem exists_inverse (h : coprime a n): ∃ k, a * k ≅ 1 :=
begin
  sorry
end

end mod_n

end hidden
