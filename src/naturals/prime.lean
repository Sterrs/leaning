import naturals.dvd naturals.induction

namespace hidden

open mynat

def prime (m: mynat) := m ≠ 1 ∧ ∀ k: mynat, k ∣ m → k = 1 ∨ k = m
def composite (m : mynat) := ∃ a b: mynat, a ≠ 1 ∧ b ≠ 1 ∧ a * b = m
def coprime (m n : mynat) := ∀ k: mynat, k ∣ m → k ∣ n → k = 1

variables m n p k : mynat

theorem zero_nprime: ¬prime 0 :=
begin
  assume h0pm,
  cases h0pm,
  have h2d0 := dvd_zero 2,
  have h2n2: 2 ≠ 2,
  have h2eq01 := h0pm_right 2 h2d0,
  repeat { cases h2eq01 },
  from h2n2 rfl,
end

theorem one_nprime: ¬prime 1 :=
begin
  assume h1pm,
  cases h1pm with h1ne1 _,
  from h1ne1 rfl,
end

theorem zero_composite: composite 0 :=
begin
  existsi zero,
  existsi zero,
  split, {
    assume h01,
    cases h01,
  }, {
    split, {
    assume h01,
    cases h01,
    },
    simp,
  },
end

theorem one_ncomposite: ¬composite 1 :=
begin
  assume h1cmp,
  cases h1cmp with a h,
  cases h with b h,
  cases h with han1 h,
  cases h with hbn1 hab1,
  from han1 (one_unit _ _ hab1),
end

theorem two_ncomposite: ¬composite 2 :=
begin
  assume h2cmp,
  cases h2cmp with a h,
  cases h with b h,
  cases h with han1 h,
  cases h with hbn1 hab2,
  cases a, {
    simp at hab2,
    cases hab2,
  }, {
    cases b, {
      simp at hab2,
      cases hab2,
    }, {
      cases a, {
        simp at han1,
        contradiction,
      }, {
        cases b, {
          simp at hbn1,
          contradiction,
        }, {
          simp at hab2,
          have h := succ_inj _ _ hab2,
          have h' := succ_inj _ _ h,
          from succ_ne_zero _ h',
        }
      }
    }
  }
end

-- prove 2 is prime by a massive case-bash
-- frankly this was just proved by going into a tactics red mist
theorem two_prime: prime 2 :=
begin
  split, {
    assume h21,
    cases h21,
      }, {
    intro k,
    assume hk2,
    cases hk2 with n hn,
    cases k, {
      simp at hn,
      cases hn,
    }, {
      cases k, {
        simp,
      }, {
        simp at hn,
        cases n, {
          simp at hn,
          cases hn,
        }, {
          simp at hn,
          cases n, {
            simp at hn,
            cc,
          }, {
            have x := succ_inj _ _ hn,
            simp at x,
            have y := succ_inj _ _ x,
            simp at y,
            exfalso, from succ_ne_zero _ (eq.symm y),
          }
        }
      }
    }
  }
end

@[symm]
theorem coprime_symm {m n : mynat} : coprime m n → coprime n m :=
begin
  assume h,
  intro k,
  assume hkn hkm,
  exact h k hkm hkn,
end

theorem coprime_one: coprime m 1 :=
begin
  intro k,
  assume _ hk,
  from dvd_one k hk,
end

theorem one_coprime: coprime 1 m :=
coprime_symm (coprime_one m)

theorem coprime_succ: coprime m (succ m) :=
begin
  intro a,
  assume hm hsucc,
  cases hm with b hb,
  cases hsucc with c hc,
  rw [←add_one_succ, hb] at hc,
  have : a ∣ 1,
    apply dvd_remainder (b * a) 1 (c * a) a,
    rw mul_comm,
    apply dvd_mul, refl,
    rw mul_comm,
    apply dvd_mul, refl,
    assumption,
  from dvd_one a this,
end
theorem succ_coprime: coprime (succ m) m :=
coprime_symm (coprime_succ m)

theorem coprime_prime:
prime p → ¬(coprime p n) → p ∣ n :=
begin
  assume hp hncp,
  sorry, -- Is this classical?
end

-- Surely classical
theorem em_prime:
prime p ∨ ¬prime p := sorry

-- Classical?
theorem nprime_imp_ncomp_or_one:
¬prime m → composite m ∨ m = 1 :=
begin
  sorry,
end

-- Requires strong induction
theorem prime_divisor:
m ≠ 1 → ∃ p : mynat, prime p ∧ p ∣ m :=
begin
  assume h,
  apply strong_induction
    (λ m, m ≠ 1 → ∃ p : mynat, prime p ∧ p ∣ m), {
    assume h,
    existsi (2:mynat),
    split, from two_prime,
    from dvd_zero 2,
  } , {
    intro n,
    assume hn hn0,
    cases em_prime (succ n) with hp hnp, {
      existsi succ n,
      split, assumption, refl,
    }, {
      have hcomp_or_one :=
        nprime_imp_ncomp_or_one (succ n) hnp,
      cases hcomp_or_one with hcomp h1, {
        cases hcomp with a h₁,
        cases h₁ with b hab,
        have ha₁ := hn a,
        have hadvds : a ∣ succ n, {
          have := hab.right.right,
          existsi b,
          symmetry,
          rw mul_comm,
          assumption,
        },
        have halen : a ≤ n, {
          apply (le_iff_lt_succ a n).mpr,
          have hasn := dvd_lt _ _ (succ_ne_zero _) hadvds,
          have hansn: a ≠ succ n, {
            -- the oldest trick in the book: just wear it down by cases
            assume hasn,
            have habsn := hab.right.right,
            simp [hasn] at habsn,
            cases b,
            simp at habsn,
            from succ_ne_zero _ (eq.symm habsn),
            cases b,
            simp at hab,
            assumption,
            simp at habsn,
            rw [←add_assoc, add_comm b n, add_assoc, ←add_succ] at habsn,
            have hcontr := add_cancel_to_zero _ _ (eq.symm habsn),
            from succ_ne_zero _ hcontr,
          },
          rw le_iff_lt_or_eq _ _ at hasn,
          cases hasn,
          assumption,
          contradiction,
        },
        have ha₂ := ha₁ halen hab.left,
        cases ha₂ with p hp,
        existsi p,
        split, from hp.left,
        from dvd_trans p a (succ n) hp.right hadvds,
      }, contradiction,
    },
  },
  assumption,
end

-- let's work our way up to primes
-- Should this be here?
theorem even_square: 2 ∣ m * m → 2 ∣ m :=
begin
  sorry
end

theorem two_only_even_prime: prime m → 2 ∣ m → m = 2 :=
begin
  assume hmpm h2dm,
  cases h2dm with n hn,
  cases m,
  rw zz at *,
  exfalso, from zero_nprime hmpm,
  have hndvds : n ∣ succ m,
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

-- Requires some form of FTA
theorem dvd_coprime:
coprime m n → m ∣ k * n → m ∣ k := sorry

theorem coprime_imp_prod_dvd:
coprime m n → m ∣ k → n ∣ k → m * n ∣ k :=
begin
  assume hcp hmk hnk,
  cases hmk with a ha,
  cases hnk with b hb,
  rw hb at ha,
  have hmb : m ∣ b,
    have hmprod : m ∣ b * n,
      rw [ha, mul_comm],
      apply dvd_mul m a,
      refl,
    apply dvd_coprime m n b,
    repeat {assumption},
  cases hmb with c hc,
  rw [hc, mul_assoc] at hb,
  existsi c, assumption,
end

end hidden
