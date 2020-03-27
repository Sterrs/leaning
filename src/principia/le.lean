import principia.mynat

namespace hidden

open mynat

def le (m n: mynat) :=  ∃ k: mynat, n = m + k
-- notation
instance: has_le mynat := ⟨le⟩

-- Given a proposition, we can say that if there are arbitrarily large mynat
-- satisfying it, then there are infinitely many satisfying it.
def infinitely_many (statement : mynat → Prop) : Prop :=
∀ n : mynat, ∃ m : mynat, n ≤ m ∧ statement m

variables m n p k : mynat

theorem zero_le: 0 ≤ m :=
begin
  existsi m,
  simp,
end

theorem le_to_add: m ≤ m + n :=
begin
  existsi n,
  refl,
end

theorem le_comb (a b c d: mynat): a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
  assume hab hcd,
  cases hab with x hx,
  cases hcd with y hy,
  existsi x + y,
  rw [hx, hy, ←add_assoc, add_assoc a x c, add_comm x c],
  repeat {rw add_assoc},
end

-- aka Horn's Lemma
theorem succ_le_succ: m ≤ n → succ m ≤ succ n :=
begin
  assume hmn,
  cases hmn with k hk,
  existsi k,
  simp [hk],
end

theorem le_add: m ≤ n → m + k ≤ n + k :=
begin
  assume hmn,
  cases hmn with d hd,
  existsi d,
  rw hd,
  repeat {rw add_assoc},
  rw add_comm d k,
end

theorem le_cancel: m + k ≤ n + k → m ≤ n :=
begin
  assume hmknk,
  cases hmknk with d hd,
  existsi d,
  repeat {rw add_comm _ k at hd},
  rw add_assoc at hd,
  from add_cancel k _ _ hd,
end

theorem le_total_order: m ≤ n ∨ n ≤ m :=
begin
  induction n, {
    repeat {rw zz},
    right,
    from zero_le m,
  }, {
    cases n_ih with hmn hnm, {
      cases hmn with k hk,
      left,
      existsi succ k,
      rw [add_succ, hk],
    }, {
      cases hnm with k hk,
      cases k, {
        left,
        existsi (1: mynat),
        simp [hk],
      }, {
        right,
        existsi k,
        simp [hk],
      },
    }
  },
end

theorem wlog_le (p: mynat → mynat → Prop) (hsymm: ∀ m n: mynat, p m n → p n m):
(∀ m n: mynat, m ≤ n → p m n) → (∀ m n: mynat, p m n) :=
begin
  assume hwlog,
  intros m n,
  cases le_total_order m n with hmn hnm, {
    from hwlog m n hmn,
  }, {
    from hsymm _ _ (hwlog n m hnm),
  }
end

-- the infamous theorem, proved intuitively via total ordering
-- can this be made tactically wlog?
theorem mul_cancel: m ≠ 0 → m * n = m * k → n = k :=
begin
  assume hmnz,
  revert n k,
  apply wlog_le (λ n k, m * n = m * k → n = k), {
    simp,
    intros n k,
    assume h hmkmn,
    from (h hmkmn.symm).symm,
  }, {
    simp,
    intros n k,
    assume hnk hmnmk,
    cases hnk with d hd,
    rw [hd, mul_add] at hmnmk,
    have hdz' := add_cancel_to_zero _ _ hmnmk,
    have hdz := mul_integral _ _ hmnz hdz',
    simp [hd, hdz],
  },
end

theorem mul_cancel_to_one: m ≠ 0 → m = m * k → k = 1 :=
begin
  assume hmn0 hmmk,
  rw [←mul_one m, mul_assoc, one_mul] at hmmk,
  rw mul_cancel m 1 k hmn0,
  assumption,
end

theorem le_mul: m ≤ n → k * m ≤ k * n :=
begin
  assume hmn,
  cases hmn with d hd,
  induction k, {
    existsi (0: mynat),
    simp,
  }, {
    existsi k_n * d + d,
    simp [hd],
  },
end

theorem le_trans: m ≤ n → n ≤ k → m ≤ k :=
begin
  assume hmn hnk,
  cases hmn with d hd,
  cases hnk with d' hd',
  existsi d + d',
  rw [hd', hd, add_assoc],
end

-- for some reason it breaks some other theorems if you add @[ref] here
theorem le_refl: m ≤ m :=
begin
  existsi (0: mynat),
  refl,
end

theorem le_zero: m ≤ 0 → m = 0 :=
begin
  assume hmlz,
  cases hmlz with d hd,
  from add_integral m d hd.symm,
end

theorem le_succ_cancel: succ m ≤ succ n → m ≤ n :=
begin
  assume hsmsn,
  cases hsmsn with d hd,
  existsi d,
  simp at hd,
  assumption,
end

theorem le_cancel_strong: m + k ≤ n → m ≤ n :=
begin
  assume hmkn,
  cases hmkn with d hd,
  existsi k + d,
  rw [hd, add_assoc],
end

theorem le_add_rhs: m ≤ n → m ≤ n + k :=
begin
  assume hmn,
  apply le_cancel_strong _ _ k,
  apply le_add _ _ k,
  assumption,
end

theorem le_one: m ≤ 1 → m = 0 ∨ m = 1 :=
begin
  assume h,
  cases h with k hk,
  cases k, {
    right,
    simp at hk,
    symmetry,
    assumption,
  }, {
    left,
    simp at hk,
    have hmk0 := succ_inj _ _ hk,
    from add_integral _ _ hmk0.symm,
  },
end

theorem le_antisymm: m ≤ n → n ≤ m → m = n :=
begin
  assume hmn hnm,
  cases hmn with d hd,
  cases hnm with d' hd',
  have hdz: d = 0, {
    rw [hd', add_assoc, add_comm _ d] at hd,
    have hzdd := add_cancel_to_zero _ _ hd,
    from add_integral _ _ hzdd,
  },
  simp [hd, hdz],
end

theorem le_mul_cancel: k ≠ 0 → k * m ≤ k * n → m ≤ n :=
begin
  assume hk0 hle,
  cases (le_total_order m n) with hmn hnm,
    assumption,
  have hknkm := le_mul n m k hnm,
  have heq := le_antisymm (k*m) (k*n) hle hknkm,
  have := mul_cancel k m n hk0 heq,
  rw this,
  from le_refl n,
end

-- I'm too lazy to prove this properly
theorem lem_nat_eq: m = n ∨ m ≠ n :=
begin
  revert m n,
  apply wlog_le, {
    intros m n,
    assume hmnmmn,
    cases hmnmmn with hnm hnnm, {
      left, from hnm.symm,
    }, {
      right,
      assume hnm,
      from hnnm hnm.symm,
    },
  }, {
    intros m n,
    assume hmn,
    cases hmn with d hd,
    cases d, {
      simp [hd],
    }, {
      right,
      rw hd,
      assume hmn,
      from succ_ne_zero _ (add_cancel_to_zero _ _ hmn),
    },
  },
end

-- how does this work??
-- instance: decidable_eq mynat


end hidden
