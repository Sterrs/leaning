import naturals.dvd

namespace hidden

open mynat

def prime (m: mynat) := m ≠ 1 ∧ ∀ k: mynat, k ∣ m → k = 1 ∨ k = m
def coprime (m n : mynat) := ∀ k: mynat, k ∣ m → k ∣ n → k = 1

variables m n p k : mynat

theorem zero_nprime: ¬ prime 0 :=
begin
    assume h0pm,
    cases h0pm,
    have h2d0 := dvd_zero 2,
    have h2n2: 2 ≠ 2,
    have h2eq01 := h0pm_right 2 h2d0,
    cases h2eq01,
    cases h2eq01,
    cases h2eq01,
    from h2n2 rfl,
end

theorem one_nprime: ¬ prime 1 :=
begin
    assume h1pm,
    cases h1pm,
    from h1pm_left rfl,
end

-- prove 2 is prime by a massive case-bash
-- frankly this was just proved by going into a tactics red mist
theorem two_prime: prime 2 :=
begin
    split,
    assume h21,
    cases h21,
    intro k,
    assume hk2,
    cases hk2 with n hn,
    cases k,
    rw [zz, mul_zero] at hn,
    cases hn,
    cases k,
    simp,
    repeat {rw mul_succ at hn},
    cases n,
    rw zz at *,
    simp at hn,
    cases hn,
    simp at hn,
    cases n,
    simp at hn,
    cc,
    have x := succ_inj _ _ hn,
    simp at x,
    have y := succ_inj _ _ x,
    rw zz at y,
    exfalso, from succ_ne_zero _ (eq.symm y),
end

theorem coprime_succ: coprime m (succ m) :=
begin
    intro a,
    assume hm hsucc,
    cases hm with b hb,
    cases hsucc with c hc,
    rw [←add_one_succ, hb] at hc,
    have : a ∣ 1,
        apply @dvd_remainder (b*a) (c*a) 1 a,
        rw mul_comm,
        apply dvd_mul, refl,
        rw mul_comm,
        apply dvd_mul, refl,
        assumption,
    from dvd_one a this,
end

theorem two_only_even_prime: prime m → 2 ∣ m → m = 2 :=
begin
    assume hmpm h2dm,
    cases h2dm with n hn,
    cases m,
    rw zz at *,
    exfalso, from zero_nprime hmpm,
    sorry,
end

-- this is pitched as a kind of long-term goal
theorem euclids_lemma: prime p → p ∣ m * n → p ∣ m ∨ p ∣ n :=
begin
    sorry
end

-- framed in a natural-numbersy sort of way.
theorem sqrt_2_irrational: n ≠ 0 → ¬m * m = n * n + n * n :=
begin
    assume hmnz hsq2q,
    have h2dvdrhs: 2 ∣ n * n + n * n,
    existsi n * n,
    -- wow refl is OP
    refl,
    sorry
end

end hidden