import principia.mynat
import principia.tactic

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
  from add_cancel hd,
end

theorem le_total_order: m ≤ n ∨ n ≤ m :=
begin
  induction n with n_n n_ih, {
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
    },
  },
end

theorem wlogle (p: mynat → mynat → Prop) (hsymm: ∀ m n: mynat, p m n → p n m):
(∀ m n: mynat, m ≤ n → p m n) → (∀ m n: mynat, p m n) :=
begin
  assume hwlog,
  intros m n,
  cases le_total_order m n with hmn hnm, {
    from hwlog m n hmn,
  }, {
    from hsymm _ _ (hwlog n m hnm),
  },
end

end hidden

-- We have to leave `hidden` to keep tactic.interactive
-- Section so that tactic stuff is not open everywhere
section wlog_tactic

open tactic
open tactic.interactive
open interactive (parse)
open interactive.types (texpr)
open lean.parser

-- Convert a goal relating two variables into two goals
-- One showing symmetry of the goal,
-- One with hypothesis m ≤ n showing the original goal.
meta def tactic.interactive.wlog_le
(m n : parse ident)
(hsymm : parse (optional (tk "with" *> ident)))
(hle : parse (optional ident)): tactic unit :=
do
  em ← get_local m,
  en ← get_local n,
  symm_name ← get_unused_name `hsymm,
  le_name ← get_unused_name `hle,
  -- And use them or whatever the tactic was provided with as
  -- optional arguments
  let symm := hsymm.get_or_else symm_name,
  let le := hle.get_or_else le_name,
  -- Revert m and n so we can apply wlogle
  revert_lst [en, em],
  -- Get the lambda expression to feed to wlogle
  la ← goal_to_lambda2,
  -- Apply wlogle
  tactic.apply `(hidden.wlogle %%la),
  -- Put everything back into context
  tactic.intro_lst [m, n, symm],
  swap,
  tactic.intro_lst [m, n, le],
  swap

end wlog_tactic

-- Return to hidden
namespace hidden

open mynat
variables m n k : mynat

-- the infamous theorem, proved intuitively via total ordering
-- can this be made tactically wlog?
theorem mul_cancel: m ≠ 0 → m * n = m * k → n = k :=
begin
  assume hmnz,
  wlog_le n k with hs hnk, {
    assume h,
    from (hs h.symm).symm,
  }, {
    assume h,
    cases hnk with d hd,
    rw [hd, mul_add] at h,
    have hdz' := add_cancel_to_zero h.symm,
    have hdz := mul_integral hmnz hdz',
    rwa [hdz, add_zero] at hd,
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
  induction k with k_n k_ih, {
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
  from add_integral hd.symm,
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
    have hmk0 := succ_inj hk,
    from add_integral hmk0.symm,
  },
end

theorem le_antisymm: m ≤ n → n ≤ m → m = n :=
begin
  assume hmn hnm,
  cases hmn with d hd,
  cases hnm with d' hd',
  have hdz: d = 0, {
    rw [hd', add_assoc, add_comm _ d] at hd,
    have hzdd := add_cancel_to_zero hd,
    from add_integral hzdd,
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

theorem lem_nat_eq: m = n ∨ m ≠ n :=
begin
  wlog_le m n with hs hmn, {
    cases hs with hnm hnnm,
      left, from hnm.symm,
    right,
    assume hnm,
    from hnnm hnm.symm,
  }, {
    cases hmn with d hd,
    cases d,
      simp [hd],
    right,
    rw hd,
    assume hmn,
    from succ_ne_zero _ (add_cancel_to_zero hmn.symm),
  },
end

end hidden
