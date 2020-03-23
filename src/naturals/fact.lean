import naturals.dvd naturals.induction

namespace hidden

open mynat

def fact: mynat → mynat
| 0        := 1
| (succ n) := (fact n) * (succ n)

variables m n p k : mynat

theorem fact_nzero:
fact m ≠ 0 :=
begin
  assume h,
  induction m with n hn,
    cases h, -- Magic?
  unfold fact at h,
  rw mul_comm at h,
  have := mul_integral (succ n) (fact n),
  from hn (this (succ_ne_zero n) h),
end

theorem fact_dvd_self {m : mynat} :
m ≠ 0 → m ∣ fact m :=
begin
  assume hneq0,
  cases m, {
    exfalso,
    simp at hneq0,
    assumption,
  }, {
    existsi (fact m),
    refl,
  },
end

theorem fact_dvd_succ (m : mynat) :
fact m ∣ fact (succ m) :=
begin
  existsi (succ m),
  rw mul_comm,
  refl,
end

theorem fact_dvd_le {m n : mynat} :
m ≤ n → fact m ∣ fact n :=
begin
  assume hlen,
  apply strong_induction (λ k, ∀ j, j ≤ k → fact j ∣ fact k), {
    assume j hjle0,
    have := le_zero j hjle0,
    rw this,
  }, {
    assume i hi j hjlesucci,
    cases (le_iff_lt_or_eq j (succ i)).mp hjlesucci, {
      have hilej : j ≤ i, {
        apply (le_iff_lt_succ j i).mpr,
        assumption,
      },
      have hilei : i ≤ i, {
        apply (le_iff_lt_or_eq i i).mpr,
        right, refl,
      },
      have h₁ := hi i hilei j hilej,
      have := fact_dvd_succ i,
      apply dvd_trans _ (fact i) _,
      assumption, assumption,
    },
    rw h,
  },
  assumption,
end

theorem fact_dvd_nlt {m n : mynat}:
m≠0 → m ≤ n → m ∣ fact n :=
begin
  assume hmne0,
  induction n with k hk, {
    assume hmle0,
    simp at hmle0,
    have hmeq0 := le_zero m hmle0,
    exfalso, contradiction,
  }, {
    assume hmlesucc,
    have hmself := fact_dvd_self hmne0,
    have hfmfsucc := fact_dvd_le hmlesucc,
    from dvd_trans m (fact m) (fact (succ k)) hmself hfmfsucc,
  }
end

theorem fact_ndvd_lt:
∀ k: mynat, k ≠ 1 → k ≤ m → ¬(k ∣ (fact m) + 1) :=
begin
  assume n hneq1 hleqm hdiv,
  cases hdiv with k hk,
  have : n ∣ 1, {
    apply dvd_remainder (fact m) 1 (k*n) n, {
      have hnne0 : n ≠ 0, {
        assume hn0,
        rw [hn0, mul_zero, add_comm] at hk,
        have : (1:mynat) = (0:mynat), {
          apply add_integral _ _ hk,
        },
        cases this,
      },
      from fact_dvd_nlt hnne0 hleqm,
    }, {
      rw mul_comm,
      apply dvd_mul n k,
      refl,
    },
    assumption,
  },
  from hneq1 (dvd_one n this),
end

end hidden