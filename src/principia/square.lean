import principia.prime

namespace hidden

open mynat

def square (m : mynat) := ∃ k : mynat, m = k * k

variables m n p k : mynat

theorem square_closed_mul:
square m → square n → square (m * n) :=
begin
  assume hm hn,
  cases hm with a ha,
  cases hn with b hb,
  existsi a * b,
  rw [ha, hb],
  rw [mul_assoc, mul_comm, mul_assoc a,
    mul_assoc b, mul_comm b a],
  simp,
end

theorem square_imp_not_prime {m : mynat}:
square m → ¬(prime m) :=
begin
  assume hs hp,
  cases hp with h1 hp,
  cases hs with a ha,
  have ham : a ∣ m,
    rw ha,
    apply dvd_mul a a, refl,
  have hor := hp a ham,
  cases hor with hm1 hmeq,
    rw [hm1, mul_one] at ha,
    contradiction,
  rw [←mul_one m, hmeq] at ha,
  have : m ≠ 0,
    assume hm0,
    have h2 := hp 2,
    rw hm0 at h2,
    have := h2 (dvd_zero 2),
    cases this, cases this, cases this,
  have := mul_cancel m 1 m this ha,
  have : m = 1,
    symmetry, assumption,
  contradiction,
end

theorem sqrt_2_not_nat: ¬m * m = 2 :=
begin
  assume h,
  have hs : square 2,
    existsi m, symmetry, assumption,
  from (square_imp_not_prime hs) two_prime,
end

end hidden
