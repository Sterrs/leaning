import .mynat

namespace hidden

open mynat

-- A bit of basic series/sum theory, not using any lists.

-- some ambitious things:
-- define polynomials
-- prove that the sums of a k-th degree polynomial are a k+1th degree polynomial

-- sum from k = 0 to n - 1 of term(k)
-- a bit unconventional, but this is the best way I could think of
-- to not have to have weird special cases with 0
def sum (term: mynat → mynat): mynat → mynat
| 0        := 0
| (succ n) := sum n + term n

variables a b c d m n k: mynat
variables term: mynat → mynat

@[simp] theorem sum_zero: sum term 0 = 0 := rfl
@[simp] theorem sum_succ: sum term (succ n) = sum term n + term n := rfl

theorem constant_sum:
sum (λ k, 1) n = n :=
begin
  induction n with n_n n_ih, {
    refl,
  }, {
    simp [n_ih],
  },
end

-- phrased in a way that avoids rationals and subtraction :)
theorem triangular_numbers:
sum (λ k, k) (succ n) * 2 = n * (n + 1) :=
begin
  induction n with n_n n_ih, {
    refl,
  }, {
    -- lots of very straightforward algebra, done in the
    -- cheekiest most unstable way possible
    rw [sum_succ, add_mul, n_ih],
    have h2ss0: 2 = succ (succ 0) := rfl,
    rw h2ss0,
    simp,
    rw [add_comm 1, add_one_succ],
    simp,
  },
end

theorem geometric_progression:
sum (λ k, a * (succ b) ^ k) n * b + a = a * (succ b) ^ n :=
begin
  induction n with n_n n_ih, {
    simp,
  }, {
    rw [sum_succ, add_mul, add_assoc, add_comm _ a, ←add_assoc, n_ih,
        mul_assoc, ←mul_add],
    conv {
      to_lhs,
      congr, skip, congr,
      rw ←mul_one (succ b ^ n_n),
    },
    rw [←mul_add, add_comm, add_one_succ, mul_comm _ (succ b)],
    simp,
  },
end

end hidden
