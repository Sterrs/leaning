-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .lt

namespace hidden

namespace mynat

def divides (m n: mynat) := ∃ k: mynat, n = k * m
instance: has_dvd mynat := ⟨divides⟩

-- gosh, how do you define gcd?
-- you should be able to define it using Euclid's algorithm and total
-- ordering of ≤
/- def gcd: mynat → mynat → mynat
| m 0 := m
| m n := if m ≤ n then gcd m (n - m)
 -/

variables {m n k p: mynat}

@[trans]
theorem dvd_trans: m ∣ n → n ∣ k → m ∣ k :=
begin
  assume hmn hnk,
  cases hmn with a ha,
  cases hnk with b hb,
  existsi a * b,
  rw [hb, ha, ←mul_assoc, mul_comm b a],
end

theorem dvd_zero: m ∣ 0 :=
begin
  existsi (0: mynat),
  rw zero_mul,
end

theorem zero_dvd: 0 ∣ m → m=0 :=
begin
  assume h,
  cases h with k hk,
  rw mul_zero at hk,
  from hk,
end

theorem one_dvd: 1 ∣ m :=
begin
  existsi m,
  refl,
end

-- Allows resolving goals of form m ∣ m by writing refl
@[refl]
theorem dvd_refl: m ∣ m :=
begin
  existsi (1: mynat),
  rw one_mul,
end

-- basically just a massive case bash to show that m and n can't be 0 or succ
-- succ of something
theorem one_unit: m * n = 1 → m = 1 :=
begin
  cases m,
  repeat {rw zz},
  rw zero_mul,
  assume h01,
  from h01,
  cases n,
  repeat {rw zz},
  rw [succ_mul, mul_zero, add_zero],
  assume h01,
  cases h01,
  cases m,
  repeat {rw zz},
  rw [mul_succ, succ_mul, zero_mul, zero_add],
  assume _,
  refl,
  cases n,
  repeat {rw zz},
  rw [mul_succ, succ_mul, succ_mul, mul_zero],
  repeat {rw add_zero},
  assume hssm, from hssm,
  -- this is the most contradictory thing I've ever seen in my life. surely
  -- there's a less overkill way
  repeat {rw succ_mul},
  repeat {rw mul_succ},
  repeat {rw add_succ},
  rw ←one_eq_succ_zero,
  assume hssssssss,
  exfalso, from succ_ne_zero (succ_inj hssssssss),
end

theorem dvd_antisymm: m ∣ n → n ∣ m → m = n :=
begin
  assume hmn hnm,
  cases hmn with a ha,
  cases hnm with b hb,
  cases n,
  rw hb,
  refl,
  have hab1: a * b = 1,
  rw hb at ha,
  rw ←mul_assoc at ha,
  -- arghh
  rw ←mul_one (succ n) at ha,
  rw mul_comm (a * b) _ at ha,
  rw mul_assoc at ha,
  have hab := mul_cancel succ_ne_zero ha,
  rw one_mul at hab,
  symmetry, assumption,
  have ha1 := one_unit hab1,
  rw [ha, ha1, one_mul],
end

theorem dvd_mul (n: mynat): k ∣ m → k ∣ m * n :=
begin
  assume hkm,
  cases hkm with a ha,
  existsi a * n,
  rw ha,
  repeat {rw mul_assoc},
  rw mul_comm k n,
end

theorem dvd_multiple: k ∣ n * k :=
begin
  rw mul_comm,
  apply dvd_mul,
  refl,
end

theorem dvd_add: k ∣ m → k ∣ m + k :=
begin
  assume hkm,
  cases hkm with n hn,
  rw hn,
  existsi n + 1,
  simp,
end

theorem dvd_cancel: k ∣ m + k → k ∣ m :=
begin
  assume hkmk,
  cases hkmk with n hn,
  cases n,
  cases k,
  rw zz at *,
  simp at hn,
  rw hn,
  rw zz at *,
  rw [zero_mul, add_comm] at hn,
  exfalso, from succ_ne_zero (add_integral hn),
  existsi n,
  rw succ_mul at hn,
  repeat {rw add_comm _ k at hn},
  from add_cancel hn,
end

theorem dvd_add_lots: k ∣ m → k ∣ m + k * n :=
begin
  induction n with n_n n_ih,
  simp,
  cc,
  simp,
  assume hkm,
  rw [add_comm k _, ←add_assoc],
  apply dvd_add _,
  from n_ih hkm,
end

theorem dvd_cancel_lots: k ∣ m + k * n → k ∣ m :=
begin
  induction n with n_n n_ih,
  simp,
  cc,
  simp,
  rw [add_comm k _, ←add_assoc],
  assume hkmksn,
  apply n_ih,
  from dvd_cancel hkmksn,
end

theorem dvd_sum: k ∣ m → k ∣ n → k ∣ m + n :=
begin
  assume hm hn,
  cases hn with a ha,
  rw [ha, mul_comm],
  apply dvd_add_lots,
  assumption,
end

theorem lt_ndvd: m ≠ 0 → m < n → ¬n ∣ m :=
begin
  assume hmnz hmn hndm,
  cases (le_total_order m n),
  cases h with d hd,
  cases d,
    rw [zz, add_zero] at hd,
    rw hd at hmn,
    from hmn le_refl,

    rw hd at hndm,
    cases hndm with a ha,
    cases a,
      simp at ha,
      from hmnz ha,
    rw succ_mul at ha,
    rw (by ac_refl : a * (m + d.succ) + (m + d.succ) =
                     m + (d.succ + a * (m + d.succ))) at ha,
    have hs0 := add_cancel_to_zero ha,
    rw succ_add at hs0,
    from succ_ne_zero hs0,

  cases h with d hd,
  cases d,
  simp at hd,
  rw hd at hmn,
  from hmn le_refl,
  rw hd at hmn,
  simp at hmn,
  have hcontr: n ≤ succ (n + d),
  existsi succ d,
  simp,
  from hmn hcontr,
end

theorem dvd_le: n ≠ 0 → m ∣ n → m ≤ n :=
begin
  assume hnn0 hmdvdn,
  cases (le_total_order m n),
  assumption,
  cases hmdvdn with k hk,
  cases h with a ha,
  rw ha at hk,
  cases a,
  existsi (0: mynat),
  simp [ha],
  simp at hk,
  cases k,
    simp at hk,
    contradiction,
  rw succ_mul at hk,
  rw (by ac_refl : k.succ + (k * n + n + k.succ * a) =
                   n + (k.succ + (k * n + k.succ * a))) at hk,
  rw succ_add at hk,
  exfalso,
  from succ_ne_zero (add_cancel_to_zero hk),
end

theorem dvd_one: m ∣ 1 → m = 1 :=
begin
  assume hm1,
  from dvd_antisymm hm1 one_dvd,
end

-- Reorder variables
-- have decided not to make implicit because it's too much of a headache
theorem dvd_remainder (m k n j : mynat):
j ∣ m → j ∣ n → m + k = n → j ∣ k :=
begin
  assume hjm hjn hmkn,
  rw ←hmkn at hjn,
  cases hjm with a ha,
  rw ha at hjn,
  rw add_comm at hjn,
  rw mul_comm at hjn,
  from dvd_cancel_lots hjn,
end

-- Useful for e.g. infinitude of primes
theorem dvd_succ_too: k ∣ m → k ∣ succ m → k=1 :=
begin
  assume hm hsucc,
  cases hm with a ha,
  cases hsucc with b hb,
  rw [←add_one_succ, ha] at hb,
  rw mul_comm a at hb,
  rw mul_comm b at hb,
  suffices : k ∣ 1,
    exact dvd_one this,
  apply dvd_remainder (k * a) 1 (k * b) k,
    apply dvd_mul a,
    refl,
    apply dvd_mul b,
    refl,
  assumption,
end

theorem dvd_succ: m ∣ succ m → m=1 :=
begin
  assume h,
  have : m ∣ m, refl,
  apply dvd_succ_too,
    refl,
  assumption,
end

end mynat

end hidden
