import naturals.mynat

namespace hidden

open mynat

-- it's kind of crazy that Lean just automatically proves this is well-defined
-- (try changing fib succ to fib succ succ)
def fib: mynat → mynat
| 0 := 0
| 1 := 1
| (succ (succ n)) := fib n + fib (succ n)

variables m n k p: mynat

-- what is the general tactical way to say to lean "just evaluate this constant
-- sub-expression please"?
@[simp] theorem fib_zero: fib 0 = 0 := rfl
@[simp] theorem fib_one: fib 1 = 1 := rfl
@[simp] theorem fib_succsucc: fib (succ (succ n)) = fib n + fib (succ n) := rfl

theorem fib_k_formula:
fib (m + k + 1) = fib k * fib m + fib (k + 1) * fib (m + 1) :=
begin
  induction k,
  repeat {rw zz},
  rw [add_zero, fib_zero, zero_mul],
  repeat {rw zero_add},
  rw [fib_one, one_mul],
  repeat {rw add_succ},
  repeat {rw succ_add},
  -- double base case required (???)
  induction k_n,
  repeat {rw zz},
  repeat {rw ←one_eq_succ_zero},
  repeat {rw add_succ},
  repeat {rw add_zero},
  repeat {rw fib_succsucc},
  simp,
  rw add_one_succ at *,
  rw add_one_succ at *,
  rw add_succ at *,
  sorry
end

end hidden
