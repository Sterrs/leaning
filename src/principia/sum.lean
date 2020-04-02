import .fib
import .nat_sub
import .fact

namespace hidden

open mynat

-- A bit of basic series/sum theory, not using any lists.

-- some ambitious things:
-- define polynomials
-- prove that the sums of a k-th degree polynomial are a k+1th degree polynomial

def sequence (α : Type) := mynat → α

namespace sequence

variable {α : Type}

-- Coerce a value into a sequence of that value.
-- e.g. ↑0 = 0, 0, 0, 0, ... = λ k, 0
-- This is probably bad so might remove this

instance: has_coe α (sequence α) := ⟨λ a, (λ k, a)⟩
@[simp] theorem coe_seq (a : α) : (↑a:sequence α) = (λ k : mynat, a) := rfl
@[simp] theorem coe_triv (a : α) (n :mynat): (↑a:sequence α) n = a := rfl

variables [has_add α] {β : Type} [has_mul β]

def add (a b : sequence α): sequence α := λ k , a k + b k
instance: has_add (sequence α) := ⟨add⟩
-- Yuck...
@[simp] theorem addition (a b : sequence α) (n : mynat) :
(a + b) n = a n + b n := rfl
@[simp] theorem coe_add (a : α) (s : sequence α) (n : mynat):
(↑a + s) n = a + (s n) := rfl
@[simp] theorem add_coe (s : sequence α) (a : α) (n : mynat):
(s + ↑a) n = (s n) + a := rfl

def mul (a b : sequence β): sequence β := λ k, a k * b k
instance: has_mul (sequence β) := ⟨mul⟩
@[simp] theorem multiplication (a b : sequence β) (n : mynat) :
(a * b) n = a n * b n := rfl
@[simp] theorem coe_mul (b : β) (s : sequence β) (n : mynat):
(↑b * s) n = b * (s n) := rfl
@[simp] theorem mul_coe (s : sequence β) (b : β) (n : mynat):
(s * ↑b) n = (s n) * b := rfl

variables [has_zero α] [has_one β]

instance: has_zero (sequence α) := ⟨λ k, 0⟩
instance: has_one (sequence β) := ⟨λ k, 1⟩

end sequence

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
@[simp] theorem sum_succ: sum term (succ n) = sum term n + term n := rfl

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

private def two : 2 = succ (succ 0) := rfl

-- phrased in a way that avoids rationals and subtraction :)
theorem triangular_numbers: ∀ n,
sum (λ k, k) (succ n) * 2 = n * (n + 1)
| zero     := rfl
| (succ n) := by conv {
  rw [sum_succ, add_mul, triangular_numbers, two],
  simp,
  rw [add_comm 1, add_one_succ],
  simp,
}

theorem geometric_progression: ∀ n,
sum (λ k, a * (succ b) ^ k) n * b + a = a * (succ b) ^ n
| zero     := by simp
| (succ n) :=
begin
  conv {
    rw [sum_succ, add_mul, add_assoc, add_comm _ a, ←add_assoc, geometric_progression,
      mul_assoc, ←mul_add],
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

-- TODO: go and clean up all the consecutive rws throughout

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
    rw this,
    rw binom_succ_succ,
    rw ←this,
    rw n_ih,
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
    rw binom_succ_succ,
    rw n_ih,
    rw binom_succ_kill,
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
    rw binom_succ_succ,
    rw n_ih,
    rw binom_succ_succ,
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
        have x := hm (succ n) k _,
        have y := hm n (succ k) _,
        conv {
          congr,
          rw binom_succ_succ,
          rw add_mul,
          rw x,
          rw ←mul_add,
          congr, skip,
          simp,
          skip,
          rw binom_succ_succ,
          rw add_mul,
          rw ←y,
          rw ←mul_add,
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
    rw add_succ,
    rw binom_succ_succ,
    rw fact_succ,
    rw mul_assoc,
    rw add_mul,
    conv {
      to_lhs,
      congr,
      rw mul_assoc,
      rw mul_comm (succ k_n),
      rw [←mul_assoc, ←mul_assoc, k_ih],
      skip,
      rw mul_comm _ (succ k_n),
      rw [←mul_assoc, ←mul_assoc, ←binom_multiplication],
      rw [mul_assoc, mul_assoc, mul_comm n],
      rw [←mul_assoc, ←mul_assoc, k_ih],
    },
    rw ←mul_add,
    rw [succ_add, fact_succ, add_comm k_n],
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
    rw sum_succ,
    rw n_ih,
    rw [add_assoc, add_comm (f 0), ←add_assoc,
        ←sum_succ],
  },
end

private theorem sum_distr': sum (λ k, f k + g k) n = (sum f n) + (sum g n) :=
sum_distr f g n

theorem binom_row_sum:
-- chad partial function notation
sum (binom n) (succ n) = 2 ^ n :=
begin
  induction n, {
    refl,
  }, {
    rw sum_succ,
    rw sum_tail,
    -- gosh this is a pain
    have: ∀ k,
      (λ k, binom (succ n_n) (succ k)) k
      = (λ k, binom n_n k + binom n_n (succ k)) k, {
      simp,
    },
    rw (sum_cancel _ _).mpr this,
    rw sum_distr',
    -- clumsy
    rw binom_succ_succ,
    rw add_comm (binom n_n n_n),
    repeat {rw ←add_assoc},
    rw add_comm,
    repeat {rw ←add_assoc},
    rw add_comm (binom n_n n_n),
    rw ←sum_succ,
    rw n_ih,
    rw [binom_succ_kill, add_zero],
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

-- this might be necessary/useful when working with -, since it lets
-- you basically assume k < n in order to rewrite the terms
theorem sum_cancel_restricted:
∀ m,
  (∀ n, n ≤ m → sum f n = sum g n) ↔
  (∀ n, n < m → f n = g n) :=
begin
  intro m,
  split, {
    assume h,
    intro n,
    assume hnm,
    have hm := h n (lt_impl_le hnm),
    have hsn := h (succ n) (lt_iff_succ_le.mp hnm),
    repeat {rw sum_succ at hsn},
    rw hm at hsn,
    from add_cancel hsn,
  }, {
    assume h,
    intro n,
    assume hnm,
    induction n, {
      refl,
    }, {
      repeat {rw sum_succ},
      rw n_ih (@le_cancel_strong n_n m 1 hnm),
      rw h n_n (lt_iff_succ_le.mpr hnm),
    },
  },
end

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
sum (λ k, binom (n + k) (2 * k)) (succ n) = fib (2 * n + 1) ∧
sum (λ k, binom (n + succ k) (2 * k + 1)) (succ n) = fib (2 * n + 2) :=
begin
  revert n,
  apply induction_conjunction, {
    from and.intro rfl rfl,
  }, {
    intro n,
    split, {
      assume odd_sum even_sum,
      rw sum_succ,
      rw sum_tail,
      have hrw:
        ∀ k,
          (λ k, binom (succ n + succ k) (2 * succ k)) k
          = (λ k, binom (n + succ k) (2 * k + 1)) k
            + (λ k, binom (n + succ k) (2 * succ k)) k, {
        intro k,
        repeat {rw lambda_subs},
        rw mul_succ,
        rw add_comm 2,
        rw add_two,
        rw add_one_succ,
        simp,
      },
      rw (sum_cancel _ _).mpr hrw, clear hrw,
      rw sum_distr',
      rw add_comm,
      repeat {rw ←add_assoc},
      have hrw:
        binom (succ n + succ n) (2 * succ n)
        = binom (n + succ n) (2 * n + 1), {
        rw mul_succ,
        rw add_comm 2,
        rw add_two,
        rw add_one_succ,
        simp [add_dupl],
        rw add_comm,
        rw add_two,
        from binom_dupl _,
      },
      conv {
        to_lhs, congr, congr,
        rw add_comm,
        rw hrw,
        rw ←sum_succ,
        rw even_sum,
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
        rw ←sum_tail n (λ k, binom (n + k) (2 * k)),
        rw odd_sum,
      }, clear hrw,
      conv {
        congr,
        rw add_comm, congr,
        rw add_one_succ,
        skip,
        rw add_two,
        skip,
        rw mul_succ,
        rw add_comm 2,
        rw add_one_succ,
        rw add_two,
        rw fib_succsucc,
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
      rw sum_distr',
      rw odd_sum,
      rw sum_succ,
      rw even_sum,
      have hrw:
        2 * succ n + 1 = succ (succ (succ (n + n))), {
        rw mul_succ,
        rw add_comm 2,
        rw add_one_succ,
        rw add_two,
        rw mul_comm,
        refl,
      },
      conv {
        congr, congr, skip, congr, skip,
        rw lambda_subs,
        congr,
        simp, skip,
        rw hrw,
      }, clear hrw,
      rw binom_succ_kill,
      rw add_zero,
      conv {
        congr, congr,
        rw mul_succ,
        rw add_comm 2,
        rw add_one_succ,
        rw add_two,
        skip,
        rw add_two,
        skip,
        rw mul_succ,
        rw add_two,
        rw add_comm,
        rw add_two,
        rw fib_succsucc,
      },
      rw add_comm,
    },
  },
end

private theorem mul_sum':
a * sum f n = sum (λ k, a * f k) n :=
begin
  rw ←mul_sum,
  sorry,
end

theorem binomial_theorem:
(a + b)^n = sum (λ k, binom n k * a^k * b^(n - k)) (succ n) :=
begin
  induction n with n_n n_ih, {
    refl,
  }, {
    rw [pow_succ, n_ih, add_mul],
    sorry,
  },
end

end naturals

end hidden
