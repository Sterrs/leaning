-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .le
import ..logic

namespace hidden

namespace mynat

def lt (m n: mynat) := ¬n ≤ m
instance: has_lt mynat := ⟨lt⟩

instance decidable_lt: ∀ m n: mynat, decidable (m < n) :=
(λ m n, not.decidable)

variables {m n p k : mynat}

theorem lt_nrefl: ¬m < m :=
(λ h, h le_refl)

theorem lt_succ_cancel: succ m < succ n → m < n :=
mp_to_contrapositive succ_le_succ

theorem lt_cancel (k: mynat): m + k < n + k → m < n :=
mp_to_contrapositive (le_add k)

theorem lt_cancel_strong: m + k < n → m < n :=
mp_to_contrapositive le_add_rhs

theorem lt_add_rhs: m < n → m < n + k :=
mp_to_contrapositive (le_cancel_strong k)

theorem nzero_iff_zero_lt: m ≠ 0 ↔ 0 < m :=
iff_to_contrapositive le_zero_iff.symm

theorem zero_lt_iff_succ: 0 < m ↔ ∃ n, m = succ n :=
by rw ←nzero_iff_zero_lt; from nzero_iff_succ

theorem lt_to_add_succ: m < m + succ n :=
begin
  assume hmmsn,
  cases hmmsn with d hd,
  rw [←add_zero m, add_assoc m _ _, add_assoc m _ _] at hd,
  have hd' := add_cancel hd,
  simp at hd',
  from succ_ne_zero hd'.symm,
end

theorem lt_nzero: ¬m < 0 := (λ h, h zero_le)

theorem zero_lt_succ: 0 < succ m := succ_nle_zero

theorem lt_add: m < n → m + k < n + k :=
mp_to_contrapositive le_cancel

theorem succ_lt_succ: m < n → succ m < succ n := @lt_add _ _ 1

theorem lt_impl_le: m < n → m ≤ n :=
begin
  assume hmn,
  cases (le_total_order m n) with hmltn hnm,
  from hmltn,
  exfalso, from hmn hnm,
end

-- pair of transformation theorems. Can be useful in a pinch
theorem le_iff_lt_succ: m ≤ n ↔ m < succ n :=
begin
  split, {
    assume hmn,
    cases hmn with d hd,
    rw hd,
    assume hmsd,
    cases hmsd with d' hd',
    rw [succ_add, add_assoc, ←add_succ,
        ←add_zero m, add_assoc] at hd',
    have hzsucc := add_cancel hd',
    rw zero_add at hzsucc,
    from succ_ne_zero hzsucc.symm,
  }, {
    assume hmsn,
    -- this total ordering theorem is crazy powerful. It feels like
    -- you need classical logic until you remember it exists
    cases (le_total_order m n) with hmn hnm,
    from hmn,
    cases hnm with d hd,
    cases d, {
      rw [hd, zz, add_zero],
    }, {
      have hsnm: succ n ≤ m,
      existsi d,
      rw [hd, add_succ, succ_add],
      exfalso, from hmsn hsnm,
    },
  },
end

theorem lt_iff_succ_le: m < n ↔ succ m ≤ n :=
begin
  split, {
    cases n, {
      assume h,
      exfalso, from lt_nzero h,
    }, {
      assume h,
      apply succ_le_succ, -- /o/
      rw le_iff_lt_succ, assumption,
    },
  }, {
    cases n, {
      assume h,
      cases h with d hd,
      exfalso, from succ_ne_zero (add_integral hd.symm),
    }, {
      assume h,
      rw ←le_iff_lt_succ,
      from le_succ_cancel h,
    },
  },
end

theorem zero_lt_one: (0 : mynat) < (1 : mynat) :=
by rw [←one_eq_succ_zero, ←le_iff_lt_succ]

-- somehow this feels like it's not using le_iff_lt_succ enough
theorem le_iff_lt_or_eq: m ≤ n ↔ m < n ∨ m = n :=
begin
  split, {
    assume hmn,
    cases hmn with d hd,
    cases d, {
      simp at hd,
      right, rw hd,
    }, {
      left,
      rw hd,
      from lt_to_add_succ,
    },
  }, {
    assume hmnmn,
    cases hmnmn, {
     from lt_impl_le hmnmn,
    }, {
      rw hmnmn,
    },
  },
end

theorem lt_iff_le_and_neq: m < n ↔ m ≤ n ∧ m ≠ n :=
begin
  split, {
    assume hmn,
    apply and.intro (lt_impl_le hmn),
    assume h,
    rw h at hmn,
    from lt_nrefl hmn,
  }, {
    assume h,
    cases h with hmn hneq,
    cases hmn with d hd,
    cases d, {
      exfalso,
      from hneq hd.symm,
    }, {
      rw lt_iff_succ_le,
      rw [hd, add_succ, ←succ_add],
      from le_to_add,
    },
  },
end

-- surely this is a library function somewhere
theorem lt_dne: ¬m < n → n ≤ m :=
begin
  by_cases (n ≤ m), {
    from (λ _, h),
  }, {
    assume h2,
    contradiction,
  },
end

theorem lt_strict: ¬(m < n ∧ n < m) :=
begin
  assume hmnnm,
  cases hmnnm with hmnnm_left hmnnm_right,
  from hmnnm_left (lt_impl_le hmnnm_right),
end

theorem lt_trichotomy: m = n ∨ m < n ∨ n < m :=
begin
  cases (le_total_order m n), {
    rw le_iff_lt_or_eq at h,
    cases h, {
      right, left, assumption,
    }, {
      left, assumption,
    },
  }, {
    rw le_iff_lt_or_eq at h,
    cases h, {
      right, right, assumption,
    }, {
      left, symmetry, assumption,
    },
  },
end

@[trans]
theorem lt_trans: m < n → n < k → m < k :=
begin
  assume hmn hnk hkm,
  cases hkm with d hd,
  cases d,
  simp at hd,
  rw hd at hmn,
  from lt_strict (and.intro hnk hmn),
  rw hd at hmn,
  have hkln: k ≤ n
  := le_cancel_strong (succ d) (lt_impl_le hmn),
  from hnk hkln,
end

theorem lt_comb {a b : mynat}: m < n → a < b → m + a < n + b :=
begin
  assume hmn hab,
  have h1: m + a < n + a, {
    apply lt_add,
    assumption,
  },
  have h2: n + a < n + b, {
    rw [add_comm n, add_comm n],
    apply lt_add,
    assumption,
  },
  from lt_trans h1 h2,
end

theorem lt_mul: k ≠ 0 → m < n → k * m < k * n :=
begin
  assume hknz hmln hknkm,
  cases hknkm with d hd,
  cases n, {
    from lt_nzero hmln,
  }, {
    rw ←le_iff_lt_succ at hmln,
    cases hmln with d' hd',
    rw [hd', mul_succ, mul_add] at hd,
    have : k + (k * m + k * d') + d = k * m + (k + k * d' + d),
      ac_refl,
    rw this at hd, clear this,
    have hcancel := add_cancel_to_zero hd,
    rw add_assoc at hcancel,
    from hknz (add_integral hcancel),
  },
end

theorem le_square: m ≤ n → m * m ≤ n * n :=
begin
  assume hle,
  have h₁ := le_mul n hle,
  have h₂ := le_mul m hle,
  rw mul_comm at h₁,
  from le_trans h₂ h₁,
end

theorem le_sqrt: m * m ≤ n * n → m ≤ n :=
begin
  assume hm2n2,
  cases (le_total_order m n), {
    assumption,
  }, {
    cases h with d hd,
    cases d, {
      simp [hd],
    }, {
      cases hm2n2 with d' hd',
      rw [hd] at hd',
      repeat { rw mul_succ at hd' <|>
               rw succ_mul  at hd' <|>
               rw mul_add  at hd' <|>
               rw add_mul  at hd' },
      have : n * n + (d * n + n) + (n + d.succ + (n * d + (d * d + d))) + d' =
             n * n + (d.succ + (d * n + n + n + n * d + d * d + d + d')),
        ac_refl,
      rw this at hd', clear this,
      have := add_cancel_to_zero hd',
      exfalso, from succ_ne_zero (add_integral this),
    },
  },
end

theorem lt_sqrt: m * m < n * n → m < n :=
begin
  assume hlt hnlem,
  have := le_square hnlem,
  contradiction,
end

theorem lt_le_chain (n : mynat): m < n → n ≤ k → m < k :=
begin
  assume hmn hnk,
  rw lt_iff_succ_le at hmn,
  rw lt_iff_succ_le,
  transitivity n,
    assumption,
  assumption,
end

theorem le_lt_chain (n : mynat): m ≤ n → n < k → m < k :=
begin
  assume hmn hnk,
  rw lt_iff_succ_le at hnk,
  rw le_iff_lt_succ at hmn,
  apply lt_le_chain (succ n),
    assumption,
  assumption,
end

theorem lt_comb_mul {a b : mynat}: m < n → a < b → m * a < n * b :=
begin
  assume hmn hab,
  rw lt_iff_succ_le at *,
  apply le_trans _ (le_mul_comb hmn hab),
  rw [mul_succ, succ_add, succ_mul, ←add_one_succ, ←add_one_succ],
  existsi m + a,
  ac_refl,
end

end mynat

end hidden
