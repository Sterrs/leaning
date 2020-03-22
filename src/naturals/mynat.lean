-- Natural numbers

-- TODO:
-- shorten things using other better tactics
-- implement more theorems about more sophisticated arithmetic (divisibility?)
-- endgame: perhaps some of the N&S course, maybe an example sheet question?

-- also, I haven't opened classical! Is it really true that none of this
-- requires classical?

-- stops name conflicts
namespace hidden

inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

-- so I can use succ instead of mynat.succ
open mynat

-- this instance stuff is pure voodoo but it seems to make the notation work
instance: has_zero mynat := ⟨zero⟩
instance: has_one mynat := ⟨succ zero⟩

def add: mynat → mynat → mynat
| m 0 := m
| m (succ n) := succ (add m n)

instance: has_add mynat := ⟨add⟩

def mul: mynat → mynat → mynat
| m 0 := 0
| m (succ n) := m + mul m n

instance: has_mul mynat := ⟨mul⟩

-- a^b should be number of functions from a b-set to an a-set. fight me
def pow: mynat → mynat → mynat
| m 0 := 1
| m (succ n) := m * pow m n

instance: has_pow mynat mynat := ⟨pow⟩

def le (m n: mynat) :=  ∃ (k: mynat), n = m + k
-- notation
instance: has_le mynat := ⟨le⟩
-- TODO: prove things about this
def lt (m n: mynat) := ¬ n ≤ m
instance: has_lt mynat := ⟨lt⟩

def divides (m n: mynat) := ∃ (k: mynat), n = k * m
instance: has_dvd mynat := ⟨divides⟩
-- take care that you must use "\mid"
def even (m: mynat) := 2 ∣ m
def prime (m: mynat) := m ≠ 1 ∧ ∀ k: mynat, k ∣ m → k = 1 ∨ k = m

variables m n k p: mynat

theorem add_zero: m + 0 = m := rfl

theorem add_succ: m + succ n = succ (m + n) := rfl

-- so for some reason all the old code breaks with the new operator instances,
-- so I have to go and replace zero with 0 wherever I used induction. How fix???
theorem zz: zero = 0 := rfl

theorem zero_add: 0 + m = m :=
begin
    induction m,
    repeat {rw zz},
    rw add_zero,
    rw [add_succ, m_ih],
end

theorem succ_add: succ m + n = succ (m + n) :=
begin
    induction n,
    refl,
    repeat {rw add_succ},
    rw n_ih,
end

theorem add_assoc: (m + n) + k = m + (n + k) :=
begin
    induction k,
    refl,
    repeat {rw add_succ},
    rw k_ih,
end

theorem add_comm: m + n = n + m :=
begin
    induction n,
    repeat {rw zz},
    rw [add_zero, zero_add],
    rw [add_succ, succ_add, n_ih],
end

theorem succ_inj: succ m = succ n → m = n :=
begin
    assume hmn,
    -- jeez this is some magic inductive type stuff
    cases hmn,
    refl,
end

theorem add_cancel: m + n = m + k → n = k :=
begin
    induction m,
    repeat {rw zz},
    repeat {rw zero_add},
    assume hnk, from hnk,
    repeat {rw succ_add},
    assume hmnmk,
    from m_ih (succ_inj _ _ hmnmk),
end

-- no idea
theorem succ_ne_zero: succ m ≠ 0 :=
begin
    cases m,
    repeat {rw zz},
    assume h10,
    cases h10,
    assume hssmz,
    cases hssmz,
end

theorem add_integral: m + n = 0 → m = 0 :=
begin
    cases m,
    repeat {rw zz},
    assume _,
    refl,
    rw succ_add,
    assume hsmnz,
    exfalso,
    from succ_ne_zero _ hsmnz,
end

theorem mul_zero: m * 0 = 0 := rfl

theorem mul_succ: m * (succ n) = m + (m * n) := rfl

theorem mul_one: m * 1 = m := rfl

theorem zero_mul: 0 * m = 0 :=
begin
    induction m,
    refl,
    rw [mul_succ, m_ih, add_zero],
end

theorem one_mul: 1 * m = m :=
begin
    induction m,
    refl,
    rw [mul_succ, m_ih],
    -- try out calc to see how it works
    calc 1 + m_n = succ 0 + m_n   : rfl
             ... = succ (0 + m_n) : by rw succ_add
             ... = succ m_n       : by rw zero_add,
end

theorem succ_mul: (succ m) * n = m * n + n :=
begin
    induction n,
    refl,
    repeat {rw mul_succ},
    rw n_ih,
    rw [add_succ, succ_add, add_assoc],
end

theorem mul_distrib: m * (n + k) = m * n + m * k :=
begin
    induction m,
    repeat {rw zz},
    repeat {rw zero_mul},
    rw add_zero,
    repeat {rw succ_mul},
    rw m_ih,
    repeat {rw add_assoc},
    rw add_comm (m_n * k) (n + k),
    rw add_comm (m_n * k) k,
    rw add_assoc,
end

theorem mul_assoc: (m * n) * k = m * (n * k) :=
begin
    induction k,
    refl,
    repeat {rw mul_succ},
    rw mul_distrib,
    rw k_ih,
end

theorem mul_comm: m * n = n * m :=
begin
    induction n,
    repeat {rw zz},
    rw [mul_zero, zero_mul],
    rw [mul_succ, succ_mul, n_ih, add_comm],
end

theorem mul_integral: m ≠ 0 → m * n = 0 → n = 0 :=
begin
    assume hmnez hmnz,
    cases n,
    repeat {rw zz},
    rw mul_succ at hmnz,
    exfalso,
    from hmnez (add_integral _ _ hmnz),
end

-- do I really have to spell out mynat like this? yuck
theorem pow_zero: m ^ (0: mynat) = 1 := rfl

theorem pow_succ: m ^ (succ n) = m * (m ^ n) := rfl

theorem zero_pow: m ≠ 0 → (0: mynat) ^ m = 0 :=
begin
    assume hmnz,
    induction m,
    contradiction,
    rw [pow_succ, zero_mul],
end

theorem pow_add: m ^ (n + k) = (m ^ n) * (m ^ k) :=
begin
    induction k,
    refl,
    rw [add_succ, pow_succ, pow_succ, k_ih],
    rw ← mul_assoc m (m ^ n) (m ^ k_n),
    rw mul_comm m (m ^ n),
    rw mul_assoc,
end

theorem pow_mul: (m ^ n) ^ k = m ^ (n * k) :=
begin
    induction k,
    refl,
    rw [pow_succ, mul_succ, pow_add, k_ih],
end

theorem mul_pow: (m * n) ^ k = m ^ k * n ^ k :=
begin
    induction k,
    refl,
    repeat {rw pow_succ},
    rw k_ih,
    rw ←mul_assoc _ n _,
    rw mul_assoc m _ n,
    rw mul_comm (m ^ k_n) n,
    repeat {rw mul_assoc},
end

theorem zero_le: 0 ≤ m :=
begin
    existsi m,
    rw zero_add,
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
    rw [hd, mul_distrib, ← add_zero (m * n), add_assoc] at hmnmk,
    have hdz' := add_cancel (m * n) 0 (0 + m * d) hmnmk,
    rw zero_add at hdz',
    have hdz := mul_integral _ _ hmnz (eq.symm hdz'),
    rw [hd, hdz, add_zero],
    -- this is basically copy-pasted (ie yanked-putted)
    cases hkn with d hd,
    -- why oh why does this rewrite BOTH the m * n
    rw [hd, mul_distrib, ← add_zero (m * k), add_assoc] at hmnmk,
    have hdz' := add_cancel (m * k) (0 + m * d) 0 hmnmk,
    rw zero_add at hdz',
    have hdz := mul_integral _ _ hmnz hdz',
    rw [hd, hdz, add_zero],
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
    rw mul_distrib,
    rw [add_assoc _ m _, ← add_assoc m _ _, add_comm m (k_n * d)],
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

theorem le_anticomm: m ≤ n ∧ n ≤ m → m = n :=
begin
    assume hmnnm,
    -- what's the nice tactical way to do this?
    have hmn := and.elim_left hmnnm,
    have hnm := and.elim_right hmnnm,
    cases hmn with d hd,
    cases hnm with d' hd',
    have hdz: d = 0,
    have hndd: n + 0 = n + d' + d,
    rw [← hd', add_zero, hd],
    apply add_integral _ d',
    apply eq.symm,
    rw add_comm,
    rw add_assoc at hndd,
    from add_cancel n _ _ hndd,
    rw [hd, hdz, add_zero],
end

theorem zero_lt: m ≠ 0 → 0 < m :=
begin
    assume hmnz hmlz,
    from hmnz (le_zero _ hmlz),
end

theorem lt_nzero: ¬ m < 0 :=
begin
    assume mlz,
    from mlz (zero_le m),
end

theorem lt_add: m < n → m + k < n + k :=
begin
    assume hmn hmknk,
    from hmn (le_cancel _ _ _ hmknk),
end

theorem lt_nrefl: ¬ m < m :=
begin
    assume hmm,
    from hmm (le_refl m),
end

theorem lt_impl_le: m < n → m ≤ n :=
begin
    assume hmn,
    apply or.elim (le_total_order m n),
    assume hmltn, from hmltn,
    assume hnm,
    exfalso, from hmn hnm,
end

theorem dvd_trans: m ∣ n → n ∣ k → m ∣ k :=
begin
    assume hmn hnk,
    cases hmn with a ha,
    cases hnk with b hb,
    existsi a * b,
    rw [hb, ha, ←mul_assoc, mul_comm b a],
end

theorem one_dvd: 1 ∣ m :=
begin
    existsi m,
    refl,
end

theorem dvd_refl: m ∣ m :=
begin
    existsi (1: mynat),
    rw one_mul,
end

theorem one_unit: m * n = 1 → m = 1 :=
begin
    sorry
end

theorem dvd_anticomm: m ∣ n → n ∣ m → m = n :=
begin
    assume hmn hnm,
    cases hmn with a ha,
    cases hnm with b hb,
    sorry
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
    have h2divrhs: 2 ∣ n * n + n * n,
    existsi n * n,
    -- wow refl is OP
    refl,
    sorry
end

end hidden
