-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .fib
import .nat_sub
import .fact
import ..sequence

namespace hidden

open mynat

-- A bit of basic series/sum theory, not using any lists.

-- some ambitious things:
-- define polynomials
-- prove that the sums of a k-th degree polynomial are a k+1th degree
-- polynomial

open sequence

section sum

-- sum from k = 0 to n - 1 of term(k)
-- a bit unconventional, but this is the best way I could think of
-- to not have to have weird special cases with 0
def sum {α : Type} [has_add α] [has_zero α]
(seq: sequence α): sequence α
| 0        := 0
| (succ n) := sum n + seq n

def product {β : Type} [has_mul β] [has_one β]
(term : sequence β) : sequence β
| 0        := 1
| (succ n) := product n * term n

end sum

section naturals
variables a b c d m n k: mynat
variables term f g : sequence mynat

@[simp] theorem sum_zero: sum term 0 = 0 := rfl

@[simp]
theorem sum_succ: sum term (succ n) = sum term n + term n := rfl

theorem constant_sum: ∀ n : mynat, sum ↑(1 :mynat) n = n
| zero := rfl
| (succ n) := by rw [sum_succ, constant_sum, coe_triv, add_one_succ]

theorem mul_sum: ∀ n, sum (↑m * f) n = m * (sum f n)
| zero := rfl
| (succ n) := by rw [sum_succ, sum_succ, mul_add, mul_sum, coe_mul]

theorem sum_distr: ∀ n, sum (f + g) n = (sum f n) + (sum g n)
| zero     := rfl
| (succ n) := by conv {
  rw [sum_succ, sum_succ, sum_succ, sum_distr, addition],
  to_rhs,
  rw [←add_assoc, add_assoc (sum f n), add_comm (f n),
      ←add_assoc (sum f n), add_assoc],
}

theorem sum_cancel: (∀ n, sum f n = sum g n) ↔ ∀ n, f n = g n :=
begin
  split, {
    assume h,
    intro n,
    have hsn := h (succ n),
    repeat {rw sum_succ at hsn},
    rw h n at hsn,
    from add_cancel hsn,
  }, {
    assume h n,
    induction n with n hn,
      refl,
    rw [sum_succ, sum_succ, hn, h n],
  },
end

theorem apply_sum: (∀ n, f n = g n) → sum f k = sum g k :=
begin
  assume h,
  induction k with k hk,
    refl,
  rw [sum_succ, sum_succ, h k, hk],
end

private def two : 2 = succ (succ 0) := rfl

-- phrased in a way that avoids rationals and subtraction :)
theorem triangular_numbers: ∀ n,
sum (λ k, succ k) n * 2 = n * (n + 1)
| zero     := rfl
| (succ n) := by conv {
  rw [sum_succ, add_mul, triangular_numbers, two],
  simp,
  rw [add_comm 1, add_one_succ],
  simp,
}

-- this one's here because it's so nice to state,
-- abeit ugly to prove
theorem cube_sum:
sum (λ k, (succ k) ^ (3: mynat)) n =
sum (λ k, succ k) n ^ (2: mynat) :=
begin
  have cancel:
    ∀ a b c: mynat,
      a = b → c + a = c + b, {
    intros a b c,
    assume hab,
    rw hab,
  },
  induction n with n hn, {
    refl,
  }, {
    rw sum_succ,
    rw sum_succ,
    rw hn,
    have hrw: (2: mynat) = succ (succ 0) := rfl,
    conv {
      congr,
      rw hrw,
      rw pow_succ,
      rw pow_succ,
      rw pow_zero,
      rw mul_one,
      skip,
      rw hrw,
      rw pow_succ,
      rw pow_succ,
      rw pow_zero,
      rw mul_one,
      rw mul_add,
      rw add_mul,
      rw add_mul,
    }, clear hrw,
    repeat {rw add_assoc},
    apply cancel,
    have hrw: ∀ a: mynat, a + a = a * 2 := (λ a, rfl),
    conv {
      to_rhs,
      rw ←add_assoc,
      congr,
      rw mul_comm,
      rw ←add_mul,
      rw hrw,
      rw triangular_numbers,
    },
    rw add_one_succ,
    conv in (succ n * succ n) {
      rw ←one_mul (succ n * succ n),
    },
    rw mul_assoc,
    rw ←add_mul,
    refl,
  },
end

theorem geometric_progression: ∀ n,
sum (λ k, a * (succ b) ^ k) n * b + a = a * (succ b) ^ n
| zero     := by simp
| (succ n) :=
begin
  conv {
    rw [sum_succ, add_mul, add_assoc, add_comm _ a,
        ←add_assoc, geometric_progression, mul_assoc, ←mul_add],
    to_lhs,
    congr, skip, congr,
    rw ←mul_one (succ b ^ n),
  },
  rw [←mul_add, add_comm, add_one_succ, mul_comm _ (succ b)],
  simp,
end

private theorem two_one : (2 : mynat) = 1 + 1 := rfl

theorem fibonacci_sum: ∀ n, (sum fib (n+1)) + 1 = (fib (n + 2))
| zero     := rfl
| (succ n) := by conv {
  congr,
  rw [succ_add, sum_succ, add_assoc, add_comm (fib (n+1)), ←add_assoc,
      fibonacci_sum, add_comm],
  skip,
  rw [succ_add, two_one, ←add_assoc n, @add_one_succ n,
      succ_add, fib_succsucc, ←add_one_succ, add_assoc n, ←two_one],
}

-- TODO: This is not the right file for this.
-- binomial coefficients, defined via Pascal's triangle,
-- so's to avoid subtraction, or worse, division!
def binom: mynat → mynat → mynat
| _        0        := 1
| 0        (succ _) := 0
| (succ n) (succ k) := binom n k + binom n (succ k)

@[simp]
theorem binom_zero: binom n 0 = 1 :=
begin
  cases n,
  refl,
  refl,
end

@[simp] theorem binom_zero_succ: binom 0 (succ n) = 0 := rfl

@[simp]
theorem binom_succ_succ:
binom (succ n) (succ k) = binom n k + binom n (succ k) := rfl

@[simp]
theorem binom_one:
binom n 1 = n :=
begin
  induction n with n_n n_ih, {
    refl,
  }, {
    have: 1 = succ 0 := rfl,
    rw [this, binom_succ_succ, ←this, n_ih],
    simp,
  },
end

@[simp]
theorem binom_overflow:
binom n (n + succ k) = 0 :=
begin
  revert k,
  induction n with n_n n_ih, {
    intro k,
    refl,
  }, {
    intro k,
    rw [add_succ, binom_succ_succ],
    conv {
      congr, congr,
      rw [succ_add, ←add_succ, n_ih],
    },
    rw succ_add,
    repeat {rw ←add_succ},
    rw n_ih,
    refl,
  },
end

@[simp]
theorem binom_succ_kill:
binom n (succ n) = 0 :=
begin
  have: 1 = succ 0 := rfl,
  rw [←add_one_succ, this, binom_overflow],
end

@[simp]
theorem binom_dupl:
binom n n = 1 :=
begin
  induction n with n_n n_ih, {
    refl,
  }, {
    rw [binom_succ_succ, n_ih, binom_succ_kill],
    refl,
  },
end

@[simp]
theorem binom_one_symm:
binom (succ n) n = succ n :=
begin
  induction n with n_n n_ih, {
    refl,
  }, {
    rw [binom_succ_succ, n_ih, binom_succ_succ],
    simp,
  }
end

theorem binom_multiplication:
binom (n + k) k * n = binom (n + k) (succ k) * (succ k) :=
begin
  induction h: n + k with m hm generalizing n k, {
    rw add_integral h,
    simp,
  }, {
    cases k, {
      simp,
      simp at h,
      assumption,
    }, {
      cases n, {
        simp at h,
        rw h,
        simp,
      }, {
        have hm_1 := hm (succ n) k _,
        have hm_2 := hm n (succ k) _,
        conv {
          congr,
          rw [binom_succ_succ, add_mul, hm_1, ←mul_add],
          congr, skip,
          simp,
          skip,
          rw [binom_succ_succ, add_mul, ←hm_2, ←mul_add],
          congr, skip,
          simp,
        }, {
          simp at h,
          simp [h],
        }, {
          simp at h,
          simp [h],
        },
      },
    },
  },
end

theorem binom_formula:
binom (n + k) k * fact k * fact n = fact (n + k) :=
begin
  induction k, {
    simp,
  }, {
    rw [add_succ, binom_succ_succ, fact_succ, mul_assoc, add_mul],
    conv {
      to_lhs,
      congr,
      rw [mul_assoc, mul_comm (succ k_n),
          ←mul_assoc, ←mul_assoc, k_ih],
      skip,
      rw [mul_comm _ (succ k_n), ←mul_assoc, ←mul_assoc,
          ←binom_multiplication, mul_assoc, mul_assoc,
          mul_comm n, ←mul_assoc, ←mul_assoc, k_ih],
    },
    rw [←mul_add, succ_add, fact_succ, add_comm k_n],
  },
end

theorem binom_symm:
binom (a + b) a = binom (a + b) b :=
begin
  apply mul_cancel, {
    have hfafb: fact a * fact b ≠ 0, {
      assume h,
      from fact_nzero (mul_integral fact_nzero h),
    },
    from hfafb,
  }, {
    rw [mul_comm, ←mul_assoc, add_comm, binom_formula,
        mul_comm, mul_comm (fact a), ←mul_assoc, add_comm,
        binom_formula],
  },
end

theorem sum_tail:
sum f (succ n) = sum (λ k, f (succ k)) n + f 0 :=
begin
  induction n, {
    rw sum_succ,
    simp,
  }, {
    rw [sum_succ, n_ih, add_assoc, add_comm (f 0), ←add_assoc,
        ←sum_succ],
  },
end

private theorem sum_distr':
sum (λ k, f k + g k) n = (sum f n) + (sum g n) :=
sum_distr f g n

-- nicer proof from binomial theorem later
example:
-- chad partial function notation
sum (binom n) (succ n) = 2 ^ n :=
begin
  induction n, {
    refl,
  }, {
    rw [sum_succ, sum_tail],
    -- gosh this is a pain
    have: ∀ k,
      (λ k, binom (succ n_n) (succ k)) k
      = (λ k, binom n_n k + binom n_n (succ k)) k, {
      simp,
    },
    rw [(sum_cancel _ _).mpr this, sum_distr',
    -- clumsy
        binom_succ_succ, add_comm (binom n_n n_n)],
    repeat {rw ←add_assoc},
    rw add_comm,
    repeat {rw ←add_assoc},
    rw [add_comm (binom n_n n_n), ←sum_succ, n_ih,
        binom_succ_kill, add_zero],
    conv in (binom (succ n_n) 0) {
      rw [binom_zero, ←binom_zero n_n],
    },
    rw add_assoc,
    rw ←sum_tail,
    rw n_ih,
    rw pow_succ,
    rw mul_comm,
    refl,
  },
end

private theorem restricted_mpr {m : mynat} {f g : sequence mynat}
(h : ∀ n, n < m → f n = g n) : ∀ n, n ≤ m → sum f n = sum g n
| zero := λ _, rfl
| (succ n) := (assume hnm, by rw [sum_succ, sum_succ,
  restricted_mpr n (@le_cancel_strong n m 1 hnm),
  h n (lt_iff_succ_le.mpr hnm)])

-- this might be necessary/useful when working with -, since it lets
-- you basically assume k < n in order to rewrite the terms
theorem sum_cancel_restricted: (∀ n, n ≤ m → sum f n = sum g n) ↔
(∀ n, n < m → f n = g n) := ⟨assume h n hnm,
have hsn : _ := h (succ n) (lt_iff_succ_le.mp hnm),
by {rw [sum_succ, sum_succ, h n (lt_impl_le hnm)] at hsn,
    from add_cancel hsn},
restricted_mpr⟩

-- β-reduction, basically
private theorem lambda_subs: (λ k, f k) k = f k := rfl
private theorem add_two: ∀ k, k + 2 = succ (succ k) := (λ k, rfl)

private theorem add_dupl: ∀ k: mynat, k + k = 2 * k :=
begin
  intro k,
  rw mul_comm,
  refl,
end

-- the famous diagonal fibonacci sums in Pascal's triangle
theorem binom_fib_sum:
sum (λ k, binom (n + k) (2 * k)) (succ n)
  = fib (2 * n + 1) ∧
sum (λ k, binom (n + succ k) (2 * k + 1)) (succ n)
  = fib (2 * n + 2) :=
begin
  revert n,
  apply induction_conjunction, {
    from and.intro rfl rfl,
  }, {
    intro n,
    split, {
      assume odd_sum even_sum,
      rw [sum_succ, sum_tail],
      have hrw:
          ∀ k,
            (λ k, binom (succ n + succ k) (2 * succ k)) k
            = (λ k, binom (n + succ k) (2 * k + 1)) k
              + (λ k, binom (n + succ k) (2 * succ k)) k, {
        intro k,
        repeat {rw lambda_subs},
        rw [mul_succ, add_comm 2, add_two, add_one_succ],
        simp,
      },
      rw [(sum_cancel _ _).mpr hrw, sum_distr', add_comm],
      clear hrw,
      repeat {rw ←add_assoc},
      have hrw:
          binom (succ n + succ n) (2 * succ n)
          = binom (n + succ n) (2 * n + 1), {
        rw [mul_succ, add_comm 2, add_two, add_one_succ],
        simp [add_dupl],
        rw [add_comm, add_two],
        from binom_dupl _,
      },
      conv {
        to_lhs, congr, congr,
        rw [add_comm, hrw, ←sum_succ, even_sum],
      }, clear hrw,
      have hrw:
          binom (succ n + 0) (2 * 0)
          = binom (n + 0) (2 * 0), {
        simp,
      },
      conv {
        to_lhs,
        rw add_assoc,
        congr, skip,
        rw hrw,
        rw [←sum_tail n (λ k, binom (n + k) (2 * k)),
            odd_sum],
      }, clear hrw,
      conv {
        congr,
        rw add_comm, congr,
        rw add_one_succ,
        skip,
        rw add_two,
        skip,
        rw [mul_succ, add_comm 2, add_one_succ,
            add_two, fib_succsucc],
      },
    }, {
      assume odd_sum_ even_sum odd_sum, clear odd_sum_,
      have hrw:
        ∀ k,
          (λ k, binom (succ n + succ k) (2 * k + 1)) k
          = (λ k, binom (succ n + k) (2 * k)) k
            + (λ k, binom (n + succ k) (2 * k + 1)) k, {
        intro k,
        simp,
      },
      rw (sum_cancel _ _).mpr hrw, clear hrw,
      rw [sum_distr', odd_sum, sum_succ, even_sum],
      have hrw:
        2 * succ n + 1 = succ (succ (succ (n + n))), {
        rw [mul_succ, add_comm 2, add_one_succ, add_two, mul_comm],
        refl,
      },
      conv {
        congr, congr, skip, congr, skip,
        rw lambda_subs,
        congr,
        simp, skip,
        rw hrw,
      }, clear hrw,
      rw [binom_succ_kill, add_zero],
      conv {
        congr, congr,
        rw [mul_succ, add_comm 2, add_one_succ, add_two],
        skip,
        rw add_two,
        skip,
        rw [mul_succ, add_two, add_comm, add_two, fib_succsucc],
      },
      rw add_comm,
    },
  },
end

private theorem mul_sum':
sum (λ k, a * f k) n = a * sum f n := mul_sum _ _ _

theorem binomial_theorem:
(a + b) ^ n = sum (λ k, binom n k * a ^ k * b ^ (n - k)) (succ n) :=
begin
  -- ok what's the one line way to do these because
  -- this is ridic
  have cancel_f:
    ∀ n k: mynat, ∀ f: mynat → mynat,
      n = k → f n = f k, {
    intros n k f,
    assume h,
    rw h,
  },
  induction n with n hn, {
    refl,
  }, {
    rw [pow_succ, hn, add_mul, ←mul_sum', ←mul_sum'],
    have hrw:
      ∀ k,
        (λ k,
          a * (binom n k * a ^ k * b ^ (n - k))
        ) k =
        (λ k,
          binom n k * a ^ succ k * b ^ (n - k)
        ) k, {
      intro k,
      repeat {rw lambda_subs},
      conv {
        to_lhs,
        rw [←mul_assoc, mul_comm _ (a ^ k)],
        congr,
        rw [←mul_assoc, ←pow_succ, mul_comm],
      },
    },
    rw (sum_cancel _ _).mpr hrw, clear hrw,
    have hrw:
      -- ??? why is it being weird about "a"
      ∀ a k, k < succ n →
        (λ k,
          b * (binom n k * a ^ k * b ^ (n - k))
        ) k =
        (λ k,
          binom n k * a ^ k * b ^ (succ n - k)
        ) k, {
      intros a k,
      assume hksn,
      repeat {rw lambda_subs},
      conv {
        to_lhs,
        rw ←mul_assoc,
        congr,
        rw mul_comm,
      },
      repeat {rw mul_assoc},
      apply cancel_f,
      apply cancel_f,
      rw ←pow_succ,
      apply cancel_f,
      cases sub_succ_converse hksn with m hm,
      have := sub_succ_cancel hm,
      rw [this, hm],
    },
    rw (sum_cancel_restricted _ _ _).mpr
       (hrw a) (succ n) le_refl, clear hrw,
    have hrw:
      ∀ a k, k < succ n →
        (λ k,
          binom n k * a ^ succ k * b ^ (n - k)
        ) k =
        (λ k,
          binom n k * a ^ succ k * b ^ (succ n - succ k)
        ) k, {
      intros a k,
      assume hksn,
      repeat {rw lambda_subs},
      rw sub_succ_succ,
    },
    rw [(sum_cancel_restricted _ _ _).mpr
          (hrw a) (succ n) le_refl,
        sum_succ, sum_tail, sum_succ, sum_tail], clear hrw,
    -- convs rearranging
    conv {
      congr,
      congr,
      rw add_comm,
      skip,
      rw add_comm,
      skip,
      rw [add_assoc, add_comm],
      congr,
      rw add_comm,
    },
    conv {
      to_lhs,
      rw ←add_assoc,
      congr,
      rw add_assoc,
      congr,
      skip,
      rw add_comm,
    },
    repeat {rw add_assoc},
    -- convs actually rewriting
    conv {
      congr,
      congr,
      rw [lambda_subs, binom_dupl, one_mul,
          sub_self_eq_zero, pow_zero, mul_one],
      skip,
      congr,
      rw [lambda_subs, binom_zero, one_mul, pow_zero,
          one_mul, sub_zero],
      skip,
      skip,
      congr,
      rw [binom_dupl, sub_self_eq_zero, pow_zero, one_mul, mul_one],
      skip,
      rw [binom_zero, pow_zero, sub_zero, one_mul, one_mul],
    },
    apply cancel_f,
    apply cancel_f,
    rw ←sum_distr',
    apply (sum_cancel _ _).mpr,
    intro k,
    repeat {rw lambda_subs},
    rw [sub_succ_succ, binom_succ_succ, ←add_mul, ←add_mul],
  },
end

-- Lovely corollary
theorem binom_sum:
sum (binom n) (succ n) = 2 ^ n :=
begin
  have hbithm := @binomial_theorem 1 1 n,
  rw ←two_one at hbithm,
  rw hbithm,
  apply apply_sum,
  assume n,
  rw [one_pow, one_pow, mul_one, mul_one],
end

theorem sum_reverse:
sum f n = sum (λ k, f (n - succ k)) n :=
begin
  have cancel_f:
    ∀ n k: mynat, ∀ f: mynat → mynat,
      n = k → f n = f k, {
    intros n k f,
    assume h,
    rw h,
  },
  revert n f,
  -- easy way to access the n - 2 case of IH
  apply duo_induction
    (λ n, ∀ f, sum f n =
      sum (λ k, f (n - succ k)) n), {
    intro f,
    refl,
  }, {
    intro f,
    refl,
  }, {
    intro n,
    assume h_ih _,
    intro f,
    rw [add_two, sum_succ, sum_tail, h_ih,
        sum_succ, sum_tail, sub_succ_succ,
        sub_zero, sub_self_eq_zero],
    conv {
      congr,
      rw [add_assoc, add_comm],
      skip,
      rw [add_assoc, add_comm],
      congr,
      rw add_comm,
    },
    apply cancel_f,
    -- help lean with type inference a bit
    have h_aesthetic := @le_refl n,
    revert h_aesthetic,
    apply (sum_cancel_restricted _ _ _).mpr,
    intro m,
    assume hmn,
    apply cancel_f,
    rw [sub_succ_succ, sub_succ_succ],
    cases sub_succ_converse hmn with d hd,
    symmetry,
    rw [sub_succ_rearrange, sub_succ, hd, succ_sub_one],
    from sub_succ_rearrange.mp hd,
  },
end

-- this has some things in common with both the binomial theorem
-- and the sum of a GP. Particularly, it's more or less a consequence
-- of the sum of a GP with common ratio in ℚ.
-- However it admits this (superficially) inductionless proof.
-- Note also that this subtraction is not what it may seem
theorem difference_of_powers:
a ^ succ n - b ^ succ n
  = (a - b) * sum (λ k, a ^ k * b ^ (n - k)) (succ n) :=
begin
  rw [sub_mul, ←mul_sum', ←mul_sum', sum_succ,
      sum_tail, sub_self_eq_zero, pow_zero, mul_one,
      pow_zero, one_mul, sub_zero],
  have hrw:
    ∀ a k, k < n →
      (λ k,
        b * (a ^ succ k * b ^ (n - succ k))
      ) k =
      (λ k,
        a * (a ^ k * b ^ (n - k))
      ) k, {
    intros a k,
    assume hkn,
    repeat {rw lambda_subs},
    rw [←mul_assoc, mul_comm b, mul_assoc,
        ←pow_succ, pow_succ a, mul_assoc],
    suffices h: n - k = succ (n - succ k), {
      rw h,
    }, {
      rw [sub_succ_rearrange, succ_add, ←add_succ],
      symmetry,
      from sub_add_condition.mpr (lt_iff_succ_le.mp hkn),
    },
  },
  rw (sum_cancel_restricted _ _ _).mpr (hrw a) _ le_refl,
  clear hrw,
  rw [sub_distr, add_comm, add_sub],
  repeat {rw pow_succ},
end

-- TODO: some sort of cross-over episode with bijections

end naturals

end hidden
