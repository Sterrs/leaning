-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .basic
import .le
import .lt

namespace hidden

namespace mynat

variables {m n k p a b c: mynat}

theorem lt_to_mul:
1 < k → n ≠ 0 → n < n * k :=
(λ h1k hnn0, lt_mul hnn0 h1k)

theorem lt_rhs_nonzero:
m < n → n ≠ 0 :=
begin
  assume hmn hn0,
  rw hn0 at hmn,
  from lt_nzero hmn,
end

-- TODO: this is now proved elsewhere
theorem lt_mul_combine:
a < b → m < n → a * m < b * n :=
begin
  assume hab hmn,
  cases m, {
    cases hbn: b * n, {
      exfalso,
      rw mul_integral (lt_rhs_nonzero hab) hbn at hmn,
      from lt_nrefl hmn,
    }, {
      from zero_lt_succ,
    },
  }, {
    have h1 := lt_mul (@succ_ne_zero m) hab,
    have h2 := lt_mul (lt_rhs_nonzero hab) hmn,
    conv at h1 {
      congr,
      rw mul_comm,
      skip,
      rw mul_comm,
    },
    from lt_trans h1 h2,
  },
end

theorem pow_gt_1:
1 < a → 1 < a ^ succ n :=
begin
  assume h1a,
  induction n, {
    from h1a,
  }, {
    rw pow_succ,
    from lt_mul_combine h1a n_ih,
  },
end

-- maybe should be done better than this
theorem pow_gt_1_converse:
1 < a ^ succ n → 1 < a :=
begin
  cases a, {
    simp,
    assume h, from h,
  }, {
    cases a, {
      simp,
      assume h, from h,
    }, {
      assume _,
      apply @lt_add _ _ 1,
      from zero_lt_succ,
    },
  },
end

theorem exp_nonzero:
a ≠ 0 → a ^ n ≠ 0 :=
begin
  assume han0 hexp0,
  induction n with n_n n_ih, {
    cases hexp0,
  }, {
    rw pow_succ at hexp0,
    from n_ih (mul_integral han0 hexp0),
  },
end

theorem exp_monotone:
1 < a → n < m → a ^ n < a ^ m :=
begin
  assume h1a hnm,
  cases (lt_iff_succ_le.mp hnm) with d hd,
  rw [hd, succ_add, ←add_succ, pow_add],
  have han0: a ≠ 0, {
    assume ha0,
    rw ha0 at h1a,
    from lt_nzero h1a,
  },
  from lt_to_mul (pow_gt_1 h1a) (exp_nonzero han0),
end

theorem lt_impl_neq:
m < n → m ≠ n :=
begin
  assume hmltn hmeqn,
  rw hmeqn at hmltn,
  from lt_nrefl hmltn,
end

theorem pow_cancel_left:  -- aka, "taking base-a logs"
1 < a → a ^ n = a ^ m → n = m :=
begin
  wlog_le m n, {
    assume h1a hanam,
    symmetry,
    from hsymm h1a hanam.symm,
  }, {
    assume h1a haman,
    cases (le_iff_lt_or_eq.mp hle) with hlt heq, {
      exfalso,
      from lt_impl_neq (exp_monotone h1a hlt) haman,
    }, {
      assumption,
    },
  },
end

theorem pow_monotone:
1 < a → n ≠ 0 → a < b → a ^ n < b ^ n :=
begin
  assume h1a hnn0 hab,
  cases n, {
    contradiction,
  }, {
    clear hnn0,
    induction n with n hn, {
      assumption,
    }, {
      conv {
        congr,
        rw pow_succ,
        skip,
        rw pow_succ,
      },
      from lt_mul_combine hab hn,
    },
  },
end

theorem pow_cancel_right: -- aka, "taking n-th roots"
1 < a → n ≠ 0 → a ^ n = b ^ n → a = b :=
begin
  assume h1a hnn0 hanbn,
  have h1b: 1 < b, {
    cases n, {
      contradiction,
    }, {
      have h1asn := pow_gt_1 h1a,
      rw hanbn at h1asn,
      from pow_gt_1_converse h1asn,
    },
  },
  wlog_le a b, {
    assume h1a hanbn h1b,
    symmetry,
    from hsymm h1b hanbn.symm h1a,
  }, {
    assume h1b hbnan h1a,
    cases (le_iff_lt_or_eq.mp hle) with hlt heq, {
      have := pow_monotone h1a hnn0 hlt,
      exfalso,
      from (lt_impl_neq this) hbnan.symm,
    }, {
      symmetry,
      assumption,
    },
  },
end

-- this is probably bad, I'm rusty
theorem root_monotone:
1 < a → n ≠ 0 → a ^ n ≤ b ^ n → a ≤ b :=
begin
  assume h1a hnn0 hanbn,
  by_contradiction,
  cases n, {
    contradiction,
  }, {
    cases b, {
      simp at hanbn,
      rw ←pow_succ at hanbn,
      have := @pow_gt_1 n a h1a,
      have := lt_le_chain _ this hanbn,
      from lt_nzero this,
    }, {
      cases b, {
        simp at hanbn,
        rw ←pow_succ at hanbn,
        have := @pow_gt_1 n a h1a,
        have := lt_le_chain _ this hanbn,
        from lt_nrefl this,
      }, {
        have h1b: 1 < b.succ.succ, {
          rw ←add_one_succ,
          rw add_comm,
          from @lt_to_add_succ 1 b,
        },
        have := pow_monotone h1b hnn0 a_1,
        contradiction,
      },
    },
  },
end

end mynat

end hidden
