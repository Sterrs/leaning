-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .prime
import .induction

namespace hidden

open mynat

def even (m: mynat) := 2 ∣ m
def odd (m: mynat) := ¬even m

variables {m n k p: mynat}

theorem even_zero: even 0 :=
begin
  existsi (0: mynat),
  simp,
end

theorem odd_one: odd 1 :=
begin
  assume he1,
  have h21 := dvd_one he1,
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
    mul_cancel_to_one succ_ne_zero,
  cases hcancel hn,
end

theorem even_add_even:
even m → even n → even (m + n) :=
begin
  assume hm hn,
  from dvd_sum hm hn,
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
  from even_add_odd hen hom,
end

theorem succ_even_is_odd: even m → odd (succ m) :=
begin
  assume hem hesm,
  cases hem with a ha,
  cases hesm with b hb,
  rw ha at hb,
  have he1: even 1, {
    have h2dvda2: 2 ∣ a * 2 := dvd_multiple,
    have h2dvdb2: 2 ∣ b * 2 := dvd_multiple,
    from dvd_remainder _ 1 _ _ h2dvda2 h2dvdb2 hb,
  },
  from odd_one he1,
end

theorem odd_periodic: odd m ↔ odd (m + 2) :=
begin
  split, {
    assume hom hem2,
    from hom (dvd_cancel hem2),
  }, {
    assume hom2 hem,
    from hom2 (dvd_add hem),
  },
end

theorem even_periodic: even m ↔ even (m + 2) :=
begin
  split, {
    assume hem,
    from dvd_add hem,
  }, {
    assume hem2,
    from dvd_cancel hem2,
  },
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
      have hon := odd_periodic.mpr hosn,
      have hesn := h_ih n (le_to_add: n ≤ n + 1) hon,
      from even_periodic.mp hesn,
    },
  },
  assumption,
end

instance even_decidable: ∀ m : mynat, decidable (even m) :=
begin
  intro m,
  induction m with m hm, {
    from is_true even_zero,
  }, {
    cases hm, {
      from is_true (succ_odd_is_even hm),
    }, {
      from is_false (succ_even_is_odd hm),
    },
  },
end

theorem cancel_succ_even: even (succ m) → odd m :=
begin
  assume hesm,
  cases m, {
    exfalso,
    from odd_one hesm,
  }, {
    apply succ_even_is_odd,
    rw even_periodic,
    assumption,
  },
end

theorem cancel_succ_odd: odd (succ m) → even m :=
begin
  assume hosm,
  cases m, {
    from even_zero,
  }, {
    apply succ_odd_is_even,
    rw odd_periodic,
    assumption,
  },
end

theorem odd_periodic_lots: even m → odd (n + m) → odd n :=
begin
  assume hem honm hen,
  from honm (even_add_even hen hem),
end

theorem even_periodic_lots: even m → even (n + m) → even n :=
begin
  assume hem honm,
  cases hem with k hk,
  rw hk at honm,
  rw mul_comm at honm,
  from dvd_cancel_lots honm,
end

theorem odd_add_odd: odd m → odd n → even (m + n) :=
begin
  assume hom hon,
  have hesm := succ_odd_is_even hom,
  have hesn := succ_odd_is_even hon,
  have hesmsn := even_add_even hesm hesn,
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
  from even_mul hem,
end

theorem odd_mul_odd:
odd m → odd n → odd (m*n) :=
begin
  assume hom hon heven,
  have hesm := succ_odd_is_even hom,
  have hesn := succ_odd_is_even hon,
  have hesmsn := even_mul_even hesm hesn,
  simp at hesmsn,
  have homn := cancel_succ_even hesmsn,
  rw ←add_assoc at homn,
  have hemn: even (m + n), {
    have hesmpsn := even_add_even hesm hesn,
    simp at hesmpsn,
    from even_periodic.mpr hesmpsn,
  },
  rw [add_comm, add_comm n m] at homn,
  have homn' := odd_periodic_lots hemn homn,
  from homn' heven,
end

-- basically we can do excluded middle without any of the classical
theorem even_square: even (m * m) → even m :=
begin
  by_cases (even m), {
    assume _,
    assumption,
  }, {
    assume hem2,
    exfalso,
    from odd_mul_odd h h hem2,
  },
end

-- this is awful
theorem sqrt_2_irrational: ¬(m ≠ 0 ∧ ∃ n, n * n = 2 * m * m) :=
begin
  -- for some reason this is a recurring lemma here
  -- is there some way to just do this inline?
  have h20: (2: mynat) ≠ 0, {
    assume h, cases h,
  },
  apply infinite_descent (λ m, m ≠ 0 ∧ ∃ n, n * n = 2 * m * m),
  intro k,
  assume h_desc,
  cases h_desc with hknz h_desc,
  cases h_desc with n hn2k2,
  -- this also comes up a lot
  have hnn0: n ≠ 0, {
    assume hn0,
    simp [hn0] at hn2k2,
    from h20 (mul_integral hknz (mul_integral hknz hn2k2.symm)),
  },
  have h2dvdn: 2 ∣ n, {
    have h2dvdn2: 2 ∣ n * n, {
      existsi k * k,
      simp [hn2k2],
    },
    from even_square h2dvdn2,
  },
  cases h2dvdn with k' hk',
  existsi k',
  split, split, {
    assume hk'0,
    simp [hk'0] at hk',
    from hnn0 hk',
  }, {
    rw hk' at hn2k2,
    existsi k,
    apply mul_cancel h20,
    rw [←mul_assoc, ←hn2k2],
    rw mul_comm 2 _,
    conv {
      to_rhs,
      rw mul_assoc,
      congr,
      rw mul_comm,
    },
  }, {
    conv at hn2k2 {
      rw hk',
      congr,
        rw mul_comm k',
        rw mul_assoc,
        skip,
      rw mul_assoc,
    },
    have h₂ := mul_cancel h20 hn2k2,
    conv at h₂ {
      to_lhs,
      rw [mul_comm, mul_assoc],
    },
    suffices : k'*k' < k*k, {
      apply lt_sqrt this,
    },
    -- TODO: write a separate theorem here
    assume hk2k'2,
    cases hk2k'2 with d hd,
    rw hd at h₂,
    have hk2e0: k * k = 0, {
      have h211: (2: mynat) = 1 + 1, refl,
      rw [h211, add_mul, one_mul, add_assoc] at h₂,
      have h' := add_cancel_to_zero h₂.symm,
      rw [add_comm, add_assoc] at h',
      from add_integral h',
    },
    from hknz (mul_integral hknz hk2e0),
  },
end

end hidden
