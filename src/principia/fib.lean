import principia.mynat
import principia.induction

namespace hidden

open mynat

-- it's kind of crazy that Lean just automatically proves this is well-defined
-- (try changing fib succ to fib succ succ)
def fib: mynat → mynat
| 0               := 0
| 1               := 1
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
  revert k,
  apply duo_induction, {
    simp,
  }, {
    simp,
    refl,
  }, {
    intro k,
    assume h_ih1 h_ih2,
    -- yucky algebra
    have: (2: mynat) = 1 + 1 := rfl,
    rw this,
    repeat {rw ←add_assoc},
    rw [add_one_succ, add_one_succ],
    rw fib_succsucc,
    rw ←add_one_succ,
    rw ←add_assoc at h_ih2,
    rw [h_ih1, h_ih2],
    -- now we have to collect the terms in F_m and F_{m + 1}
    conv {
      to_lhs,
      rw add_assoc,
      rw add_comm,
      congr, congr, skip,
      rw add_comm,
    },
    rw ←add_assoc,
    rw ←add_mul,
    conv {
      to_lhs,
      congr, congr, congr, congr, skip,
      rw add_one_succ,
    },
    rw ←fib_succsucc,
    rw add_assoc,
    rw ←add_mul,
    conv {
      to_lhs,
      congr, skip, congr,
      rw add_comm,
      rw add_one_succ,
    },
    rw ←fib_succsucc,
    rw add_comm,
    refl,
  },
end

end hidden
