import .dvd
import .mul

namespace hidden
open myint

-- a and b are congruent modulo n
def cong (n a b : myint) : Prop := ∃ k : myint, a = b + n * k

-- Throughout this section we will work modulo n
section mod_n

-- Fix a value n, which we will work modulo
parameter {n : myint}
-- Write ≅ for congruent modulo n
local infix `≅`:50 := cong n

variables {a b c x y z : myint}

@[refl]
theorem cong_refl : a ≅ a :=
begin
  existsi (0 : myint),
  rw [myint.mul_zero, myint.add_zero],
end

@[symm]
theorem cong_symm : a ≅ b → b ≅ a :=
begin
  assume h,
  cases h with k hk,
  existsi -k,
  rw mul_neg,
  rw ←(@myint.add_cancel _ _ (n * k)),
  rw [myint.add_assoc, myint.neg_self_add, myint.add_zero],
  symmetry,
  assumption,
end

@[trans]
theorem cong_trans : a ≅ b → b ≅ c → a ≅ c :=
begin
  assume hab hbc,
  cases hab with k hk,
  cases hbc with m hm,
  rw [hm, myint.add_assoc, ←myint.mul_add] at hk,
  existsi m + k,
  assumption,
end

theorem cong_self_to_zero : n ≅ 0 :=
begin
  existsi (1:myint),
  rw [myint.zero_add, myint.mul_one],
end

theorem cong_add_same : a ≅ b → a + c ≅ b + c :=
begin
  assume h,
  cases h with k hk,
  unfold cong,
  rw hk,
  existsi k,
  repeat {rw add_assoc},
  rw add_comm _ c,
end

theorem cong_add : a ≅ b → x ≅ y → a + x ≅ b + y :=
begin
  assume hab hxy,
  transitivity a + y,
  repeat {rw add_comm a},
  from cong_add_same hxy,
  rw add_comm y,
  from cong_add_same hab,
end

theorem cong_mul_same : a ≅ b → c * a ≅ c * b :=
begin
  assume hab,
  cases hab with k hk,
  existsi (k * c),
  rw hk,
  rw mul_add,
  rw mul_comm c (n * k),
  rw mul_assoc,
end

theorem cong_mul : a ≅ b → x ≅ y → a * x ≅ b * y :=
begin
  assume hab hxy,
  transitivity a * y,
  from cong_mul_same hxy,
  repeat {rw mul_comm _ y},
  from cong_mul_same hab,
end


theorem cong_zero_iff_dvd : a ≅ 0 ↔ n ∣ a :=
begin
  split; assume h, {
    cases h with k hk,
    existsi k,
    rw hk,
    rw zero_add,
    rw mul_comm,
  }, {
    cases h with k hk,
    existsi k,
    rw hk,
    rw zero_add,
    rw mul_comm,
  },
end

-- Euclid's Lemma
theorem exists_inverse (h : coprime a n): ∃ k, a * k ≅ 1 :=
begin
  sorry
end

end mod_n

end hidden
