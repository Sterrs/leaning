import principia.lt
import logic.basic

namespace hidden

open mynat

-- proof of the princple of strong induction
-- conceptually quite nice: works by showing that for any N, the statement will
-- hold for all M less than or equal to that N.
theorem strong_induction
(statement: mynat → Prop)
(base_case: statement 0)
(inductive_step: ∀ n: mynat,
                  (∀ m: mynat, m ≤ n → statement m)
                    → statement (succ n)):
∀ k: mynat, statement k :=
begin
  intro k,
  have h_aux: ∀ N: mynat, (∀ M: mynat, M ≤ N → statement M), {
    intro N,
    induction N with N_n N_ih, {
      simp,
      intro M,
      assume hMl0,
      have hM0 := le_zero _ hMl0,
      rw hM0,
      from base_case,
    }, {
      intro M,
      assume hMlesN,
      cases hMlesN with d hd,
      cases d, {
        simp at hd,
        rw ←hd,
        from inductive_step N_n N_ih,
      }, {
        have hMleN: M ≤ N_n, {
          existsi d,
          simp at hd,
          assumption,
        },
        from N_ih M hMleN,
      },
    }
  },
  from h_aux (succ k) k (le_to_add k 1),
end

-- induction with n base cases.
-- Note the case with n = 0 is basically a direct proof,
-- the case with n = 1 is regular induction.
-- This is currently a bit of a pain to actually use, particularly for proving
-- bases cases, hence the below special case. It would be really cool to have a
-- tactic to just split the base cases into goals ^_^
theorem multi_induction
(n: mynat)
(statement: mynat → Prop)
-- statement is true for 0, ..., n - 1
(base_cases: ∀ m: mynat, m < n → statement m)
-- given the statement for m, ..., m + n - 1, the statement holds for m + n
(inductive_step: ∀ m: mynat,
  (∀ d: mynat, d < n → statement (m + d)) → statement (m + n)):
∀ m: mynat, statement m :=
begin
  -- I'm not sure if this proof is the nicest way to go
  apply strong_induction, {
    -- yuckily, the base case depends on if n is 0 or not
    cases n, {
      apply inductive_step,
      intro d,
      assume hd0,
      from false.elim (lt_nzero _ hd0),
    }, {
      apply base_cases,
      from zero_lt_succ _,
    },
  }, {
    intro m,
    cases (le_lem n (succ m)) with hnm hmn, {
      cases hnm with d hd,
      rw hd,
      assume h_sih,
      rw add_comm,
      apply inductive_step,
      -- at this point it just takes a bit of wrangling to show the obvious
      intro d',
      assume hdn,
      apply h_sih,
      rw [le_iff_lt_succ, hd, add_comm],
      from lt_add _ _ d hdn,
    }, {
      assume _,
      from base_cases _ hmn,
    },
  },
end

-- theorem for convenience
theorem duo_induction
(statement: mynat → Prop)
(h0: statement 0)
(h1: statement 1)
(inductive_step: ∀ m: mynat,
  statement m → statement (m + 1) → statement (m + 2)):
∀ m: mynat, statement m :=
begin
  apply multi_induction 2, {
    -- grind out base cases
    intro m,
    cases m, {
      assume _, assumption,
    }, {
      cases m, {
        assume _, assumption,
      }, {
        assume hcontr,
        exfalso, from lt_nzero _ (lt_cancel m 0 2 hcontr),
      },
    },
  }, {
    intro m,
    intro hd,
    apply inductive_step, {
      apply hd 0,
      from zero_lt_succ 1,
    }, {
      apply hd 1,
      from lt_add _ _ 1 (zero_lt_succ 0),
    },
  },
end

open classical
local attribute [instance] prop_decidable

-- Should help prove Bezout
theorem well_ordering
(statement : mynat → Prop) :
(∃ k : mynat, statement k) →
∃ k : mynat, statement k ∧
∀ j : mynat, (statement j) →  k ≤ j :=
begin
  assume hex,
  by_contradiction h,
  rw not_exists at h,
  -- Prove by strong_induction that it's true for all
  -- if there is no smallest for which it is false.
  have hall : ∀ k : mynat, ¬(statement k), {
    apply strong_induction (λ k, ¬statement k), {
      assume hs0,
      have h0 := h 0,
      rw not_and at h0,
      have hcontra := h0 hs0,
      suffices : ∀ (j : mynat), statement j → 0 ≤ j,
        contradiction,
      intro j,
      assume _,
      from zero_le j,
    }, {
      assume n hn hsucc,
      have hnall := (not_and.mp (h (succ n))) hsucc,
      cases not_forall.mp hnall with x hnx,
      cases not_imp.mp hnx with hx hnotsucclex,
      have hxlen : x ≤ n, {
        have hxltsucc : x < succ n, from hnotsucclex,
        rw ←le_iff_lt_succ at hxltsucc, assumption,
      },
      have hcontra := hn x hxlen,
      contradiction,
    },
  },
  cases hex with k hk,
  have hnk := hall k,
  contradiction,
end

-- Intuitionist given well-ordering
theorem infinite_descent
(statement : mynat → Prop) :
(∀ k : mynat, (statement k → ∃ j : mynat, statement j ∧ j < k))
→ ∀ k : mynat, ¬(statement k) :=
begin
  assume h k hk,
  have hex : ∃ k : mynat, statement k ∧
             ∀ j : mynat, (statement j) →  k ≤ j, {
    apply well_ordering,
    existsi k,
    assumption,
  },
  cases hex with i hi,
  cases hi with hil hir,
  have hallile := h i hil,
  cases hallile with j hj,
  cases hj with hjl hjr,
  have := hir j hjl,
  contradiction,
end

end hidden
