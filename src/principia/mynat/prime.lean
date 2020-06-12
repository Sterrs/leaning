-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .dvd
import .induction
import .fact

namespace hidden

open mynat

def prime (m: mynat) := m ≠ 1 ∧ ∀ k: mynat, k ∣ m → k = 1 ∨ k = m
def composite (m : mynat) := ∃ a b: mynat, a ≠ 1 ∧ b ≠ 1 ∧ a * b = m
def coprime (m n : mynat) := ∀ k: mynat, k ∣ m → k ∣ n → k = 1

variables {m n p k : mynat}

theorem zero_nprime: ¬prime 0 :=
begin
  assume h0pm,
  cases h0pm with h0pm_left h0pm_right,
  have h2d0: (2: mynat) ∣ 0 := dvd_zero,
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
  from han1 (one_unit hab1),
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
          have h := succ_inj hab2,
          have h' := succ_inj h,
          from succ_ne_zero h',
        },
      },
    },
  },
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
            have hcontr' := succ_inj hn.symm,
            simp at hcontr',
            have hcontr := succ_inj hcontr',
            simp at hcontr,
            exfalso, from succ_ne_zero hcontr,
          },
        },
      },
    },
  },
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
  from dvd_one hk,
end

theorem one_coprime: coprime 1 m :=
coprime_symm coprime_one

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
  from dvd_one this,
end

theorem succ_coprime: coprime (succ m) m :=
coprime_symm coprime_succ

theorem coprime_prime:
prime p → ¬(coprime p n) → p ∣ n :=
begin
  assume hp hncp,
  sorry, -- Is this classical?
end

open classical

local attribute [instance] prop_decidable

lemma nprime_imp_ncomp_or_one:
¬prime m → composite m ∨ m = 1 :=
begin
  assume h,
  cases not_and_distrib.mp h with heq hnall, {
    right,
    from not_not.mp heq,
  }, {
    left,
    cases not_forall.mp hnall with k hk,
    cases not_imp.mp hk with hkdvdm heq1m,
    cases hkdvdm with a hak,
    existsi a,
    existsi k,
    split, {
      assume ha1,
      rw [ha1, one_mul] at hak,
      have : k = 1 ∨ k = m,
        right, symmetry, assumption,
      contradiction,
    }, split, {
      assume hk1,
      have : k = 1 ∨ k = m,
        left, assumption,
      contradiction,
    }, {
      symmetry, assumption,
    },
  },
end

-- Requires strong induction
theorem prime_divisor:
m ≠ 1 → ∃ p: mynat, prime p ∧ p ∣ m :=
begin
  assume h,
  apply strong_induction
    (λ m, m ≠ 1 → ∃ p: mynat, prime p ∧ p ∣ m), {
    assume h,
    existsi (2: mynat),
    split, from two_prime,
    from dvd_zero,
  }, {
    intro n,
    assume hn hn0,
    cases em (prime (succ n)) with hp hnp, {
      existsi succ n,
      split, assumption, refl,
    }, {
      have hcomp_or_one :=
        nprime_imp_ncomp_or_one hnp,
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
        have halen: a ≤ n, {
          apply le_iff_lt_succ.mpr,
          have hasn := dvd_le succ_ne_zero hadvds,
          have hansn: a ≠ succ n, {
            -- the oldest trick in the book: just wear it down by
            -- cases
            assume hasn,
            have habsn := hab.right.right,
            simp [hasn] at habsn,
            cases b,
            simp at habsn,
            from succ_ne_zero habsn.symm,
            cases b,
            simp at hab,
            assumption,
            simp at habsn,
            rw [←add_assoc, add_comm b n,
                add_assoc, ←add_succ] at habsn,
            have hcontr := add_cancel_to_zero habsn.symm,
            from succ_ne_zero hcontr,
          },
          rw le_iff_lt_or_eq at hasn,
          cases hasn,
          assumption,
          contradiction,
        },
        have ha₂ := ha₁ halen hab.left,
        cases ha₂ with p hp,
        existsi p,
        split, from hp.left,
        from dvd_trans hp.right hadvds,
      }, contradiction,
    },
  },
  assumption,
end

theorem infinitude_of_primes:
infinitely_many prime :=
begin
  -- Famously, this is a proof by contradiction
  by_contradiction h,
  -- As there are only finitely many primes, there exists an n than
  -- which there is no prime greater
  cases not_forall.mp h with n hn,
  -- So any x greater than n is not prime
  have halln : ∀ x, n ≤ x → ¬prime x, {
    have := not_exists.mp hn,
    assume x hnx hpx,
    have hx := this x,
    from hx ⟨hnx, hpx⟩,
  },
  -- We can form a contradiction if we can exhibit a k which is not 1,
  -- and is not divisible by anything less than n except 1
  suffices:
      ∃ k : mynat, k ≠ 1 ∧ ∀ x : mynat, x ≠ 1 → x ≤ n → ¬(x ∣ k), {
    cases this with k h₁,
    have hk := h₁.right,
    -- and is not divisible by any prime
    have hnoprimediv : ∀ p : mynat, prime p → ¬(p ∣ k), {
      -- Since assume we have some prime divisor p
      assume p hp,
      -- If p were more than n, it wouldn't be prime
      have := halln p,
      -- And it's greater than or equal to n
      by_cases (n ≤ p), {
        -- Which is a contradiction,
        exfalso,
        from this h hp,
      }, {
        -- Or less than or equal to n, so doesn't divide k!
        from hk p hp.left (lt_impl_le h),
      },
    },
    -- Which directly contradicts the fact that every natural > 1 is
    -- divisible by a prime
    have hprimediv := prime_divisor h₁.left,
    cases hprimediv with p hp,
    from hnoprimediv p hp.left hp.right,
  },
  -- Exhibit (fact n) + 1, and we are done.
  existsi (fact n) + 1,
  split, {
    assume h₁,
    have heq := h₁.symm,
    clear h₁,
    rw add_comm at heq,
    suffices : fact n = 0,
      from fact_nzero this,
    apply add_cancel_to_zero,
    assumption,
  },
  from fact_ndvd_lt,
end

-- this is pitched as a kind of long-term goal
theorem euclids_lemma: prime p → p ∣ m * n → p ∣ m ∨ p ∣ n :=
begin
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
      apply dvd_mul,
      refl,
    apply dvd_coprime,
    repeat {assumption},
  cases hmb with c hc,
  rw [hc, mul_assoc] at hb,
  existsi c, assumption,
end

end hidden
