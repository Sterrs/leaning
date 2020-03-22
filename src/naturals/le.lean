import naturals.mynat

namespace hidden

open mynat

def le (m n: mynat) :=  ∃ (k: mynat), n = m + k
-- notation
instance: has_le mynat := ⟨le⟩

variables m n p k : mynat

theorem zero_le: 0 ≤ m :=
begin
    existsi m,
    rw zero_add,
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
    rw [succ_add, hk],
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
    induction n,
    repeat {rw zz},
    right,
    from zero_le m,
    cases n_ih,
    cases n_ih with k hk,
    left,
    existsi succ k,
    rw [add_succ, hk],
    cases n_ih with k hk,
    cases k,
    left,
    existsi succ 0,
    rw hk,
    rw add_succ,
    refl,
    right,
    existsi k,
    rw [hk, succ_add, add_succ],
end

-- the infamous theorem, proved intuitively via total ordering
-- can this be made wlog?
theorem mul_cancel: m ≠ 0 → m * n = m * k → n = k :=
begin
    assume hmnz,
    assume hmnmk,
    cases (le_total_order n k) with hnk hkn,
    cases hnk with d hd,
    -- why oh why does this rewrite BOTH the m * n
    rw [hd, mul_add, ←add_zero (m * n), add_assoc] at hmnmk,
    have hdz' := add_cancel (m * n) 0 (0 + m * d) hmnmk,
    rw zero_add at hdz',
    have hdz := mul_integral _ _ hmnz (eq.symm hdz'),
    rw [hd, hdz, add_zero],
    -- this is basically copy-pasted (ie yanked-putted)
    cases hkn with d hd,
    -- why oh why does this rewrite BOTH the m * n
    rw [hd, mul_add, ←add_zero (m * k), add_assoc] at hmnmk,
    have hdz' := add_cancel (m * k) (0 + m * d) 0 hmnmk,
    rw zero_add at hdz',
    have hdz := mul_integral _ _ hmnz hdz',
    rw [hd, hdz, add_zero],
end

theorem mul_cancel_to_one: m ≠ 0 → m = m * k → k = 1 :=
begin
    assume h0 h,
    rw [←mul_one m, mul_assoc, one_mul] at h,
    rw mul_cancel m 1 k,
    repeat {assumption},
end

theorem le_mul: m ≤ n → k * m ≤ k * n :=
begin
    assume hmn,
    cases hmn with d hd,
    induction k,
    repeat {rw zz},
    existsi (0: mynat),
    repeat {rw zero_mul},
    refl,
    repeat {rw succ_mul},
    repeat {rw hd},
    existsi k_n * d + d,
    rw mul_add,
    rw [add_assoc _ m _, ←add_assoc m _ _, add_comm m (k_n * d)],
    repeat {rw add_assoc},
end

theorem le_trans: m ≤ n → n ≤ k → m ≤ k :=
begin
    assume hmn hnk,
    cases hmn with d hd,
    cases hnk with d' hd',
    existsi d + d',
    rw [hd', hd, add_assoc],
end

theorem le_refl: m ≤ m :=
begin
    existsi (0: mynat),
    refl,
end

theorem le_zero: m ≤ 0 → m = 0 :=
begin
    assume hmlz,
    cases hmlz with d hd,
    from add_integral m d (eq.symm hd),
end

theorem le_succ_cancel: succ m ≤ succ n → m ≤ n :=
begin
    assume hsmsn,
    cases hsmsn with d hd,
    existsi d,
    simp at hd,
    from hd,
end

theorem le_cancel_strong: m + k ≤ n → m ≤ n :=
begin
    assume hmkn,
    cases hmkn with d hd,
    existsi k + d,
    rw hd,
    rw add_assoc,
end

theorem le_add_rhs: m ≤ n → m ≤ n + k :=
begin
    assume hmn,
    apply le_cancel_strong _ _ k,
    apply le_add _ _ k,
    cc,
end

theorem le_one: m ≤ 1 → m = 0 ∨ m = 1 :=
begin
    assume h,
    cases h with k hk,
    cases k,
        simp at hk,
        right, symmetry,
        assumption,
    -- Have to manually show 1 = m + succ k → 1 = 1 + (m + k)
    rw [←add_one_succ, ←add_assoc] at hk,
    rw add_comm at hk,
    have sum0 := (add_cancel_to_zero 1 (m+k)) hk,
    left,
    from add_integral m k sum0,
end

theorem le_anticomm: m ≤ n → n ≤ m → m = n :=
begin
    assume hmn hnm,
    cases hmn with d hd,
    cases hnm with d' hd',
    have hdz: d = 0,
    have hndd: n + 0 = n + d' + d,
    rw [←hd', add_zero, hd],
    apply add_integral _ d',
    apply eq.symm,
    rw add_comm,
    rw add_assoc at hndd,
    from add_cancel n _ _ hndd,
    rw [hd, hdz, add_zero],
end

end hidden
