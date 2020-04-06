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

@[simp]
theorem nat_nat_mul: (↑a : myint) * ↑b = ↑(a * b) := rfl

@[simp]
theorem nat_neg_mul: ↑a * -[1+ b] = -(↑(a * succ b)) := rfl

@[simp]
theorem neg_nat_mul: -[1+ a] * ↑b = -(↑(succ a * b)) := rfl

@[simp]
theorem neg_neg_mul: -[1+ a] * -[1+ b] = ↑((succ a) * succ b) := rfl

-- Why is this rfl
theorem mul_zero : ∀ {m : myint}, m * 0 = 0
| (of_nat a) := rfl
| -[1+ a] := rfl

-- But this isn't rfl???
theorem zero_mul : ∀ {m : myint}, 0 * m = 0
| (of_nat a) :=
by rw [←zero_nat,←coe_nat_eq, nat_nat_mul, hidden.zero_mul]
| -[1+ a] :=
by rw [←zero_nat, nat_neg_mul, hidden.zero_mul, zero_nat, neg_zero]

theorem mul_one: ∀ {m : myint}, m * 1 = m
| (of_nat a) := rfl
| -[1+ a] := rfl

theorem one_mul : ∀ {m: myint},1 * m = m
| (of_nat a) :=
by rw [←one_nat, ←coe_nat_eq, nat_nat_mul, hidden.one_mul]
| -[1+ a] :=
by rw [←one_nat, nat_neg_mul, hidden.one_mul, neg_coe_succ]

-- Stupid but useful
private theorem one: 1 = succ 0 := one_eq_succ_zero.symm

theorem mul_neg_one: ∀ {m : myint}, m * (-1) = -m
| (of_nat a) :=
by rw [neg_one, ←coe_nat_eq, nat_neg_mul, ←one, hidden.mul_one]
| -[1+ a] :=
by rw [neg_one, neg_neg_mul, ←one, hidden.mul_one, neg_neg_succ]

theorem neg_one_mul: ∀ {m : myint}, (-1) * m = -m
| (of_nat a) :=
by rw [←coe_nat_eq, neg_one, neg_nat_mul, ←one, hidden.one_mul]
| -[1+ a] :=
by rw [neg_one, neg_neg_mul, ←one, hidden.one_mul, neg_neg_succ]

theorem mul_comm: ∀ {m n : myint}, m * n = n * m
| (of_nat a) (of_nat b) :=
by rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_mul, nat_nat_mul,
       hidden.mul_comm]
| (of_nat a) -[1+ b] :=
by rw [←coe_nat_eq, nat_neg_mul, neg_nat_mul, hidden.mul_comm]
| -[1+ a] (of_nat b) :=
by rw [←coe_nat_eq, nat_neg_mul, neg_nat_mul, hidden.mul_comm]
| -[1+ a] -[1+ b] :=
by rw [neg_neg_mul, neg_neg_mul, hidden.mul_comm]

-- rfl is magic
-- This is a "helper" lemma for mul_assoc
private lemma mul_neg_nat: ∀ {m:myint} {a:mynat}, m * -↑a = -(m * ↑a)
| (of_nat b) zero := rfl
| (of_nat b) (succ a) := rfl
| -[1+ b] zero := rfl
| -[1+ b] (succ a) :=
by rw [neg_coe_succ, neg_neg_mul, neg_nat_mul, neg_neg]

-- These are much simpler than the addition ones, mostly just repeatedly
-- using the basic rules.
theorem mul_assoc: ∀ {m n k : myint}, m * n * k = m * (n * k)
| (of_nat a) (of_nat b) (of_nat c) :=
by repeat {rw nat_nat_mul <|> rw ←coe_nat_eq}; rw hidden.mul_assoc
| (of_nat a) (of_nat b) -[1+ c]    :=
by rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_mul, nat_neg_mul, nat_neg_mul,
       mul_neg_nat, nat_nat_mul, hidden.mul_assoc]
| (of_nat a) -[1+ b]    (of_nat c) :=
by rw [←coe_nat_eq, ←coe_nat_eq, nat_neg_mul, neg_nat_mul, mul_comm,
       mul_neg_nat, mul_neg_nat, nat_nat_mul, nat_nat_mul,
       hidden.mul_comm, hidden.mul_assoc]
| (of_nat a) -[1+ b]    -[1+ c]    :=
by rw [←coe_nat_eq, nat_neg_mul, neg_neg_mul, nat_nat_mul, mul_comm,
       mul_neg_nat, neg_nat_mul, neg_neg, hidden.mul_comm,
       hidden.mul_assoc]
| -[1+ a]    (of_nat b) (of_nat c) :=
by rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_mul, neg_nat_mul, mul_comm,
       mul_neg_nat, nat_nat_mul, neg_nat_mul, hidden.mul_comm,
       hidden.mul_assoc]
| -[1+ a]    (of_nat b) -[1+ c]    :=
by rw [←coe_nat_eq, neg_nat_mul, nat_neg_mul, mul_comm, mul_neg_nat,
       mul_neg_nat, neg_nat_mul, neg_nat_mul, neg_neg, neg_neg,
       hidden.mul_comm, hidden.mul_assoc]
| -[1+ a]    -[1+ b]    (of_nat c) :=
by rw [←coe_nat_eq, neg_neg_mul, neg_nat_mul, mul_neg_nat, neg_nat_mul,
       neg_neg, nat_nat_mul, hidden.mul_assoc]
| -[1+ a]    -[1+ b]    -[1+ c]    := by
rw [neg_neg_mul, neg_neg_mul, nat_neg_mul, neg_nat_mul, hidden.mul_assoc]

theorem mul_neg : m * (-n) = - (m * n) :=
by rw [←mul_neg_one, ←mul_assoc, ←@neg_one_mul (m*n), mul_comm]

theorem neg_mul : (-m) * n = - (m * n) :=
by rw [mul_comm, @mul_comm m, mul_neg]

theorem mul_add : m * (n + k) = m * n + m * k := sorry

theorem add_mul : (m + n) * k = m * k + n * k :=
by rw [mul_comm, @mul_comm m, @mul_comm n, mul_add]


end myint
end hidden
