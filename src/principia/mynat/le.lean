-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .basic
import ..tactic

namespace hidden

namespace mynat

def le (m n: mynat) :=  ∃ k: mynat, n = m + k
-- notation
instance: has_le mynat := ⟨le⟩

-- Given a proposition, we can say that if there are arbitrarily large
-- mynat satisfying it, then there are infinitely many satisfying it.
def infinitely_many (statement : mynat → Prop) : Prop :=
∀ n : mynat, ∃ m : mynat, n ≤ m ∧ statement m

variables {m n p k : mynat}

theorem zero_le: 0 ≤ m :=
exists.intro m (zero_add m).symm

theorem succ_nle_zero: ¬(succ m ≤ 0) :=
begin
  assume hsm0,
  cases hsm0 with d hd,
  from succ_ne_zero (add_integral hd.symm),
end

theorem le_to_add: m ≤ m + n :=
exists.intro n rfl

@[refl]
theorem le_refl: m ≤ m := @le_to_add _ 0

theorem le_eq_refl: m = n → m ≤ n := (λ h, h ▸ le_refl)

theorem le_succ: m ≤ succ m := @le_to_add _ 1

@[trans]
theorem le_trans: m ≤ n → n ≤ k → m ≤ k :=
begin
  assume hmn hnk,
  cases hmn with d hd,
  cases hnk with d' hd',
  existsi d + d',
  rw [hd', hd, add_assoc],
end

theorem le_add (k: mynat): m ≤ n → m + k ≤ n + k :=
begin
  assume hmn,
  cases hmn with d hd,
  existsi d,
  rw hd,
  repeat {rw add_assoc},
  rw add_comm d k,
end

theorem le_comb {a b c d: mynat}: a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
  assume hab hcd,
  transitivity (b + c),
    from le_add c hab,
  rwa [add_comm, add_comm b],
  from le_add b hcd,
end

theorem le_add_converse (k: mynat): ¬(m ≤ n) → ¬(m + k ≤ n + k) :=
begin
  assume hnot hmknk,
  apply hnot,
  cases hmknk with d hd,
  existsi d,
  rw [add_assoc, add_comm k, ←add_assoc] at hd,
  from add_cancel_right hd,
end

-- aka Horn's Lemma
theorem succ_le_succ: m ≤ n → succ m ≤ succ n :=
le_add 1

theorem sls_converse: ¬(m ≤ n) → ¬(succ m ≤ succ n) :=
le_add_converse 1

instance decidable_le: ∀ m n: mynat, decidable (m ≤ n) :=
begin
  intros m n,
  induction m with m hm generalizing n, {
    from is_true zero_le,
  }, {
    induction n with n hn generalizing m, {
      from is_false succ_nle_zero,
    }, {
      cases (hm n) with hnot h, {
        from is_false (sls_converse hnot),
      }, {
        from is_true (succ_le_succ h),
      },
    },
  },
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

theorem le_total_order (m n: mynat): m ≤ n ∨ n ≤ m :=
begin
  induction n with n_n n_ih, {
    repeat {rw zz},
    right,
    from zero_le,
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

theorem wlogle
(p: mynat → mynat → Prop)
(hsymm: ∀ m n: mynat, p m n → p n m):
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

end mynat

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
  tactic.apply `(hidden.mynat.wlogle %%la),
  -- Put everything back into context
  tactic.intro_lst [m, n, symm],
  swap,
  tactic.intro_lst [m, n, le],
  swap

end wlog_tactic

-- Return to hidden
namespace hidden

namespace mynat

variables {m n k: mynat}

theorem le_mul (k: mynat): m ≤ n → k * m ≤ k * n :=
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

theorem le_to_mul (k: mynat): k ≠ 0 → m ≤ k * m :=
begin
  assume hkn0,
  cases k, {
    exfalso,
    from hkn0 rfl,
  }, {
    existsi k * m,
    rw [succ_mul, add_comm],
  },
end

theorem le_rhs_mul (k: mynat): k ≠ 0 → m ≤ n → m ≤ k * n :=
begin
  assume hkn0 hmn,
  from le_trans hmn (le_to_mul k hkn0),
end

theorem le_zero: m ≤ 0 → m = 0 :=
begin
  assume hmlz,
  cases hmlz with d hd,
  from add_integral hd.symm,
end

theorem le_zero_iff: m ≤ 0 ↔ m = 0 :=
iff.intro le_zero le_eq_refl

theorem le_succ_cancel: succ m ≤ succ n → m ≤ n :=
begin
  assume hsmsn,
  cases hsmsn with d hd,
  existsi d,
  simp at hd,
  assumption,
end

theorem le_cancel_strong (k: mynat): m + k ≤ n → m ≤ n :=
begin
  assume hmkn,
  cases hmkn with d hd,
  existsi k + d,
  rw [hd, add_assoc],
end

theorem le_add_rhs: m ≤ n → m ≤ n + k :=
begin
  assume hmn,
  apply le_cancel_strong k,
  apply le_add k,
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

theorem le_mul_comb {a b : mynat}: m ≤ n → a ≤ b → m * a ≤ n * b :=
begin
  assume hmn hab,
  transitivity (m * b),
    from le_mul m hab,
  have hmbnb := le_mul b hmn,
  rwa [mul_comm, @mul_comm n],
end

theorem le_mul_cancel: k ≠ 0 → k * m ≤ k * n → m ≤ n :=
begin
  assume hk0 hle,
  cases (le_total_order m n) with hmn hnm,
    assumption,
  have hknkm := le_mul k hnm,
  have heq := le_antisymm hle hknkm,
  have := mul_cancel hk0 heq,
  rw this,
end

end mynat

end hidden
