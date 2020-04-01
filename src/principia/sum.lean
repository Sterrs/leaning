import .fib
import .nat_sub

namespace hidden

open mynat

-- A bit of basic series/sum theory, not using any lists.

-- some ambitious things:
-- define polynomials
-- prove that the sums of a k-th degree polynomial are a k+1th degree polynomial

def sequence (α : Type) := mynat → α

-- sum from k = 0 to n - 1 of term(k)
-- a bit unconventional, but this is the best way I could think of
-- to not have to have weird special cases with 0
def sum {α : Type} [has_zero α] [has_add α]
(term: sequence α): sequence α
| 0        := 0
| (succ n) := sum n + term n

variables a b c d m n k: mynat
variables term f g : mynat → mynat

@[simp] theorem sum_zero: sum term 0 = 0 := rfl
@[simp] theorem sum_succ: sum term (succ n) = sum term n + term n := rfl

theorem constant_sum: ∀ n, sum (λ k, (1:mynat)) n = n
| zero := rfl
| (succ n) := by simp [constant_sum n]

theorem mul_sum: ∀ n, sum (λ k, m * f k) n = m * (sum f n)
| zero := rfl
| (succ n) := by rw [sum_succ, sum_succ, mul_add, mul_sum]

theorem sum_distr: ∀ n, sum (λ k, f k + g k) n = (sum f n) + (sum g n)
| zero     := rfl
| (succ n) := by conv {
  rw [sum_succ, sum_succ, sum_succ, sum_distr], to_rhs,
  rw [←add_assoc, add_assoc (sum f n), add_comm (f n),
      ←add_assoc (sum f n), add_assoc],
}

theorem sum_cancel: (∀ n, sum f n = sum g n) ↔ ∀ n, f n = g n :=
begin
  split, {
    assume h n,
    induction n with n hn, {
      have := h (succ zero),
      dsimp only [sum] at this,
      simp at this,
      from this,
    }, {
      have := h (succ (succ n)),
      repeat { rw sum_succ at this },
      rw [hn, h n] at this,
      from add_cancel this,
    },
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

end hidden
