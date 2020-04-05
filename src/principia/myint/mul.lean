import .add


namespace hidden
namespace myint

open mynat
open myint

variables {m n k : myint}
variables {a b c : mynat}

def mul: myint → myint → myint
| (of_nat m) (of_nat n) := of_nat (m * n)
| -[1+ m] (of_nat n)    := neg_of_nat (succ m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m] -[1+ n]       := of_nat (succ m * succ n)

instance: has_mul myint := ⟨mul⟩

theorem mul_zero : m * 0 = 0 := sorry

theorem zero_mul : 0 * m = 0 := sorry

theorem mul_one : m * 1 = m :=
begin
  cases m,
    dsimp [mul],
    sorry,
  sorry,
end

theorem one_mul : 1 * m = m := sorry

theorem mul_neg : m * (-n) = - (m * n) := sorry

theorem neg_mul : (-m) * n = - (m * n) := sorry

theorem mul_add : m * (n + k) = m * n + m * k := sorry

theorem add_mul : (m + n) * k = m * k + n * k := sorry


end myint
end hidden
