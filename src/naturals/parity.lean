import naturals.prime

namespace hidden

open mynat

def even (m: mynat) := 2 ∣ m
def odd (m: mynat) := ¬even m

variables m n k p: mynat

theorem two_only_even_prime: prime m → 2 ∣ m → m = 2 :=
begin
  assume hmpm h2dm,
  cases h2dm with n hn,
  cases m,
  rw zz at *,
  exfalso, from zero_nprime hmpm,
  have hndvds: n ∣ succ m,
    rw hn,
    apply dvd_mul, refl,
  cases hmpm with hsneq1 hdiv,
  have h₂ := hdiv n hndvds,
  cases h₂,
    rw [h₂, one_mul] at hn,
    assumption,
  exfalso,
  rw h₂ at hn,
  have hcancel :=
    mul_cancel_to_one (succ m) 2 (succ_ne_zero m),
  cases hcancel hn,
end

theorem even_add_even:
even m → even n → even (m + n) :=
begin
  assume hm hn,
  from dvd_sum _ _ _ hm hn,
end

theorem even_remainder (m k n : mynat):
even m → even n → m + k = n → even k :=
begin
  assume hm hn h,
  from dvd_remainder _ _ _ _ hm hn h,
end

theorem even_add_odd:
even m → odd n → odd (m + n) :=
begin
  assume hm hn heven,
  have : even n, {
    apply even_remainder m n (m + n) hm heven,
    refl,
  },
  contradiction,
end

theorem even_mul:
even m → even (m * n) :=
begin
  assume hm,
  cases hm with a ha,
  existsi a * n,
  rw ha,
  simp,
end

theorem odd_mul_odd:
odd m → odd n → odd (m*n) :=
begin
  assume hm hn heven,
  sorry, -- Euclid?
end

open classical

local attribute [instance] prop_decidable

theorem even_square: 2 ∣ m * m → 2 ∣ m :=
begin
  assume h,
  by_contradiction hndvd,
  have := not_exists.mp hndvd,
  sorry,
end

end hidden
