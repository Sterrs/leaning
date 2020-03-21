-- stops name comflicts
namespace hidden

inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

-- so I can use succ instead of mynat.succ
open mynat

-- this instance stuff is pure voodoo but it seems to make the notation work
instance: has_zero mynat := ⟨zero⟩
instance: has_one mynat := ⟨succ zero⟩

def add: mynat → mynat → mynat
| m 0 := m
| m (succ n) := succ (add m n)

instance: has_add mynat := ⟨add⟩

def mul: mynat → mynat → mynat
| m 0 := 0
| m (succ n) := m + mul m n

instance: has_mul mynat := ⟨mul⟩

-- a^b should be number of functions from a b-set to an a-set. fight me
def pow: mynat → mynat → mynat
| m 0 := 1
| m (succ n) := m * pow m n

variables m n k: mynat

theorem add_zero: m + 0 = m := rfl

theorem add_succ: m + succ n = succ (m + n) := rfl

-- so for some reason all the old code breaks with the new operator instances,
-- so I have to go and replace zero with 0 wherever I used induction. How fix???
theorem zz: zero = 0 := rfl

theorem zero_add: 0 + m = m :=
begin
    induction m,
    repeat {rw zz},
    rw add_zero,
    rw [add_succ, m_ih],
end

theorem succ_add: succ m + n = succ (m + n) :=
begin
    induction n,
    repeat {rw zz},
    repeat {rw add_zero},
    repeat {rw add_succ},
    rw n_ih,
end

theorem add_assoc: (m + n) + k = m + (n + k) :=
begin
    induction k,
    repeat {rw zz},
    repeat {rw add_zero},
    repeat {rw add_succ},
    rw k_ih,
end

theorem add_comm: m + n = n + m :=
begin
    induction n,
    repeat {rw zz},
    rw [add_zero, zero_add],
    rw [add_succ, succ_add, n_ih],
end

theorem mul_zero: m * 0 = 0 := rfl

theorem mul_succ: m * (succ n) = m + (m * n) := rfl

theorem mul_one: m * 1 = m := rfl

theorem zero_mul: 0 * m = 0 :=
begin
    induction m,
    repeat {rw zz},
    rw mul_zero,
    rw [mul_succ, m_ih, add_zero],
end

theorem one_mul: 1 * m = m :=
begin
    induction m,
    repeat {rw zz},
    rw mul_zero,
    rw [mul_succ, m_ih],
    calc 1 + m_n = succ 0 + m_n   : rfl
             ... = succ (0 + m_n) : by rw succ_add
             ... = succ m_n       : by rw zero_add,
end

theorem succ_mul: (succ m) * n = m * n + n :=
begin
    induction n,
    repeat {rw zz},
    repeat {rw mul_zero},
    rw add_zero,
    repeat {rw mul_succ},
    rw n_ih,
    rw [add_succ, succ_add, add_assoc],
end

theorem mul_distrib: m * (n + k) = m * n + m * k :=
begin
    induction m,
    repeat {rw zz},
    repeat {rw zero_mul},
    rw add_zero,
    repeat {rw succ_mul},
    rw m_ih,
    repeat {rw add_assoc},
    rw add_comm (m_n * k) (n + k),
    rw add_comm (m_n * k) k,
    rw add_assoc,
end

theorem mul_assoc: (m * n) * k = m * (n * k) :=
begin
    induction k,
    repeat {rw zz},
    repeat {rw mul_zero},
    repeat {rw mul_succ},
    rw mul_distrib,
    rw k_ih,
end

theorem mul_comm: m * n = n * m :=
begin
    induction n,
    repeat {rw zz},
    rw [mul_zero, zero_mul],
    rw [mul_succ, succ_mul, n_ih, add_comm],
end

theorem pow_zero: pow m 0 = 1 := rfl

theorem pow_succ: pow m (succ n) = m * (pow m n) := rfl

theorem zero_pow: m ≠ 0 → pow 0 m = 0 :=
begin
    intro hmnz,
    induction m,
    contradiction,
    rw [pow_succ, zero_mul],
end

theorem pow_add: pow m (n + k) = (pow m n) * (pow m k) :=
begin
    induction k,
    repeat {rw zz},
    rw [add_zero, pow_zero, mul_one],
    rw [add_succ, pow_succ, pow_succ, k_ih],
    rw ← mul_assoc m (pow m n) (pow m k_n),
    rw mul_comm m (pow m n),
    rw mul_assoc,
end

end hidden
