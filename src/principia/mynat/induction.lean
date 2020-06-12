-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .lt
import ..logic

namespace hidden

open mynat

-- proof of the principle of strong induction
-- conceptually quite nice: works by showing that for any N, the
-- statement will hold for all M less than or equal to that N.
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
      have hM0 := le_zero hMl0,
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
    },
  },
  from h_aux (succ k) k (le_to_add: k ≤ k + 1),
end

-- very similar. Formulating it in terms of the strict ordering
-- makes the prerequisites seem easier, but my hot take is that
-- this one is secretly much less nice
theorem strict_strong_induction
(statement: mynat → Prop)
(inductive_step: ∀ n: mynat,
                  (∀ m: mynat, m < n → statement m)
                    → statement n):
∀ k: mynat, statement k :=
begin
  apply strong_induction, {
    apply inductive_step,
    intro m,
    assume hm0,
    exfalso,
    from lt_nzero hm0,
  }, {
    intro n,
    assume h_ih,
    apply inductive_step,
    intro m,
    assume hmsn,
    apply h_ih,
    rw le_iff_lt_succ,
    assumption,
  },
end

-- can this be done in an even flashier one-term sort of way?
-- it must be possible, right
theorem lt_well_founded : well_founded lt :=
begin
  split,
  intro a,
  apply strict_strong_induction,
  intro n,
  assume h_ih,
  split,
  assumption,
end

instance: has_well_founded mynat := ⟨lt, lt_well_founded⟩


-- induction with n base cases.
-- Note the case with n = 0 is basically a direct proof,
-- the case with n = 1 is regular induction.
-- This is currently a bit of a pain to actually use, particularly for
-- proving bases cases, hence the below special case. It would be
-- really cool to have a tactic to just split the base cases into
-- goals ^_^
theorem multi_induction
(n: mynat)
(statement: mynat → Prop)
-- statement is true for 0, ..., n - 1
(base_cases: ∀ m: mynat, m < n → statement m)
-- given the statement for m, ..., m + n - 1, the statement holds for
-- m + n
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
      exfalso, from lt_nzero hd0,
    }, {
      apply base_cases,
      from zero_lt_succ,
    },
  }, {
    intro m,
    by_cases (n ≤ (succ m)), {
      cases h with d hd,
      rw hd,
      assume h_sih,
      rw add_comm,
      apply inductive_step,
      -- at this point it just takes a bit of wrangling to show the
      -- obvious
      intro d',
      assume hdn,
      apply h_sih,
      rw [le_iff_lt_succ, hd, add_comm],
      from lt_add hdn,
    }, {
      assume _,
      from base_cases _ h,
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
        exfalso, from lt_nzero (lt_cancel 2 hcontr),
      },
    },
  }, {
    intro m,
    intro hd,
    apply inductive_step, {
      apply hd 0,
      from zero_lt_succ,
    }, {
      apply hd 1,
      from lt_add zero_lt_succ,
    },
  },
end

-- oddly specific convenient way to prove conjunctive statements
-- about mynat
theorem induction_conjunction
(p q: mynat → Prop)
(base_case: p 0 ∧ q 0)
(inductive_step:
  ∀ n, (p n → q n → p (succ n)) ∧
       (p n → q n → p (succ n) → q (succ n))):
∀ n, p n ∧ q n :=
begin
  intro n,
  induction n, {
    from base_case,
  }, {
    have hpsn := (inductive_step n_n).left n_ih.left n_ih.right,
    split, {
      from hpsn,
    }, {
      from (inductive_step n_n).right n_ih.left n_ih.right hpsn,
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
      from zero_le,
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

theorem descend_to_zero (p : mynat → Prop)
(hdec: ∀ {k}, p (succ k) → p k)
: ∀ {m}, p m → p 0
| zero := assume h, by assumption
| (succ m) := assume h, descend_to_zero (hdec h)

end hidden
