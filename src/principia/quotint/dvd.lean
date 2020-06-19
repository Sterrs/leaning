import ..mynat.dvd
import .max

namespace hidden
namespace quotint

def dvd (m n : quotint) := ∃ k : quotint, n = k * m

instance: has_dvd quotint := ⟨dvd⟩

def coprime (m n : quotint) := ∀ k: quotint, k ∣ m → k ∣ n → (k = 1 ∨ k = -1)

variables m n k : quotint

theorem int_dvd_iff_abs_dvd :
m ∣ n ↔ (abs m) ∣ (abs n) :=
begin
  split; assume h, {
    cases h with k hk,
    existsi (abs k),
    sorry,
  }, {
    cases h with k hk,
    sorry,
  },
end

@[trans]
theorem dvd_trans {m n k : quotint}: m ∣ n → n ∣ k → m ∣ k :=
begin
  assume hmn hnk,
  cases hmn with a ha,
  cases hnk with b hb,
  existsi a * b,
  rw [hb, ha, ←mul_assoc, mul_comm b a],
end

theorem dvd_zero: m ∣ 0 :=
begin
  existsi (0: quotint),
  rw zero_mul,
end

theorem zero_dvd {m : quotint}: 0 ∣ m → m=0 :=
begin
  assume h,
  cases h with k hk,
  rw mul_zero at hk,
  from hk,
end

theorem one_dvd: 1 ∣ m :=
begin
  existsi m,
  rw mul_one,
end

@[refl]
theorem dvd_refl: m ∣ m :=
begin
  existsi (1: quotint),
  rw one_mul,
end

theorem dvd_mul {k m : quotint}: k ∣ m → k ∣ m * n :=
begin
  assume hkm,
  cases hkm with a ha,
  existsi a * n,
  rw ha,
  repeat {rw mul_assoc},
  rw mul_comm k n,
end

theorem dvd_mul_right {k m : quotint}: k ∣ m → k ∣ n * m :=
λ h, by rw mul_comm; from dvd_mul _ h

theorem dvd_multiple: k ∣ n * k :=
begin
  rw mul_comm,
  apply dvd_mul,
  refl,
end

theorem dvd_sum: k ∣ m → k ∣ n → k ∣ m + n :=
begin
  assume hm hn,
  cases hm with a ha, subst ha,
  cases hn with b hb, subst hb,
  existsi (a + b),
  rw add_mul,
end

-- Reorder variables
-- have decided not to make implicit because it's too much of a headache
theorem dvd_remainder (j m n k : quotint):
j ∣ m → j ∣ n → m + k = n → j ∣ k :=
begin
  sorry,
end

theorem coe_coe_dvd {a b : mynat} : a ∣ b ↔ (↑a : quotint) ∣ ↑b :=
begin
  split; assume h, {
    cases h with k hk,
    subst hk,
    rw ←coe_coe_mul,
    from dvd_mul_right _ (by refl),
  }, {
    sorry,
  },
end

end quotint
end hidden
