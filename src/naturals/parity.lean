import naturals.prime
import naturals.induction

namespace hidden

open mynat

def even (m: mynat) := 2 ∣ m
def odd (m: mynat) := ¬even m

variables m n k p: mynat

theorem even_zero: even 0 :=
begin
  existsi (0: mynat),
  simp,
end

theorem odd_one: odd 1 :=
begin
  assume he1,
  have h21 := dvd_one _ he1,
  cases h21,
end

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

theorem odd_add_even:
odd m → even n → odd (m + n) :=
begin
  assume hom hen,
  rw add_comm,
  from even_add_odd _ _ hen hom,
end

theorem succ_even_is_odd: even m → odd (succ m) :=
begin
  assume hem hesm,
  cases hem with a ha,
  cases hesm with b hb,
  rw ha at hb,
  have he1: even 1, {
    have h2dvda2 := dvd_multiple a 2,
    have h2dvdb2 := dvd_multiple b 2,
    from dvd_remainder _ 1 _ _ h2dvda2 h2dvdb2 hb,
  },
  from odd_one he1,  
end

theorem odd_periodic: odd m ↔ odd (m + 2) :=
begin
  split, {
    assume hom hem2,
    from hom (dvd_cancel _ _ hem2),
  }, {
    assume hom2 hem,
    from hom2 (dvd_add _ _ hem),
  },
end

theorem even_periodic: even m ↔ even (m + 2) :=
begin
  split, {
    assume hem,
    from dvd_add _ _ hem,
  }, {
    assume hem2,
    from dvd_cancel _ _ hem2,
  }
end

-- is this overkill?
theorem succ_odd_is_even: odd m → even (succ m) :=
begin
  assume hom,
  apply strong_induction  (λ m, odd m → even (succ m)), {
    assume ho0,
    exfalso,
    from ho0 even_zero,
  }, {
    intro n,
    assume h_ih,
    assume hosn,
    cases n, {
      existsi (1: mynat),
      refl,
    }, {
      have hon := (odd_periodic _).mpr hosn,
      have hesn := h_ih n (le_to_add _ 1) hon,
      from (even_periodic _).mp hesn,
    }
  },
  assumption,
end

theorem odd_or_even: even m ∨ odd m :=
begin
  induction m, {
    left, from even_zero,
  }, {
    cases m_ih with hem hom,
    right, from succ_even_is_odd _ hem,
    left, from succ_odd_is_even _ hom,
  },
end

theorem cancel_succ_even: even (succ m) → odd m :=
begin
  assume hesm,
  cases m,
  exfalso,
  from odd_one hesm,
  apply succ_even_is_odd,
  rw even_periodic,
  assumption,
end

theorem cancel_succ_odd: odd (succ m) → even m :=
begin
  assume hosm,
  cases m,
  from even_zero,
  apply succ_odd_is_even,
  rw odd_periodic,
  assumption,
end

theorem odd_periodic_lots: even m → odd (n + m) → odd n :=
begin
  assume hem honm hen,
  from honm (even_add_even _ _ hen hem),
end

theorem even_periodic_lots: even m → even (n + m) → even n :=
begin
  assume hem honm,
  cases hem with k hk,
  rw hk at honm,
  rw mul_comm at honm,
  from dvd_cancel_lots _ _ _ honm,
end

theorem odd_add_odd: odd m → odd n → even (m + n) :=
begin
  assume hom hon,
  have hesm := succ_odd_is_even _ hom,
  have hesn := succ_odd_is_even _ hon,
  have hesmsn := even_add_even _ _ hesm hesn,
  simp at hesmsn,
  rw even_periodic,
  from hesmsn,
end

theorem even_mul: even m → even (m * n) :=
begin
  assume hm,
  cases hm with a ha,
  existsi a * n,
  rw ha,
  simp,
end

theorem even_mul_even: even m → even n → even (m * n) :=
begin
  assume hem _,
  from even_mul _ _ hem,
end

theorem odd_mul_odd:
odd m → odd n → odd (m*n) :=
begin
  assume hom hon heven,
  have hesm := succ_odd_is_even _ hom,
  have hesn := succ_odd_is_even _ hon,
  have hesmsn := even_mul_even _ _ hesm hesn,
  simp at hesmsn,
  have homn := cancel_succ_even _ hesmsn,
  rw ←add_assoc at homn,
  have hemn: even (m + n),
  have hesmpsn := even_add_even (succ m) (succ n) hesm hesn,
  simp at hesmpsn,
  from (even_periodic _).mpr hesmpsn,
  rw [add_comm, add_comm n m] at homn,
  have homn' := odd_periodic_lots _ _ hemn homn,
  from homn' heven,
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
