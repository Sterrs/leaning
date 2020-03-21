inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

-- so I can use succ instead of mynat.succ
open mynat

def add: mynat → mynat → mynat
| m zero := m
| m (succ n) := succ (add m n)

def mul: mynat → mynat → mynat
| m zero := zero
| m (succ n) := add m (mul m n)

-- a^b should be number of functions from a b-set to an a-set. fight me
def pow: mynat → mynat → mynat
| m zero := succ zero
| m (succ n) := mul m (pow m n)

variables m n k: mynat

-- It's probably bad style to make these theorems but idk how else I'm
-- supposed to refer to these things. Also how do I make it so I can just
-- call it add_zero? And how do I get nice infix notation and make it so I
-- can write 0?
theorem add_zero2: add m zero = m :=
begin
    refl,
end

theorem add_succ2: add m (succ n) = succ (add m n) :=
begin
    refl,
end

theorem zero_add2: add zero m = m :=
begin
    induction m,
    rw add_zero2,
    rw [add_succ2, m_ih],
end

theorem succ_add2: add (succ m) n = succ (add m n) :=
begin
    induction n,
    repeat {rw add_zero2},
    repeat {rw add_succ2},
    rw n_ih,
end

theorem add_assoc2: add (add m n) k = add m (add n k) :=
begin
    induction k,
    repeat {rw add_zero2},
    repeat {rw add_succ2},
    rw k_ih,
end

theorem add_comm2: add m n = add n m :=
begin
    induction n,
    rw [add_zero2, zero_add2],
    rw [add_succ2, succ_add2, n_ih],
end

theorem mul_zero2: mul m zero = zero :=
begin
    refl,
end

theorem mul_succ2: mul m (succ n) = add m (mul m n) :=
begin
    refl,
end

theorem zero_mul2: mul zero m = zero :=
begin
    induction m,
    rw mul_zero2,
    rw [mul_succ2, m_ih, add_zero2],
end

theorem succ_mul2: mul (succ m) n = add (mul m n) n :=
begin
    induction n,
    repeat {rw mul_zero2},
    rw add_zero2,
    repeat {rw mul_succ2},
    rw n_ih,
    rw [add_succ2, succ_add2, add_assoc2],
end

theorem mul_distrib2: mul m (add n k) = add (mul m n) (mul m k) :=
begin
    induction m,
    repeat {rw zero_mul2},
    rw add_zero2,
    repeat {rw succ_mul2},
    rw m_ih,
    repeat {rw add_assoc2},
    rw add_comm2 (mul m_n k) (add n k),
    rw add_comm2 (mul m_n k) k,
    rw add_assoc2,
end

theorem mul_assoc2: mul (mul m n) k = mul m (mul n k) :=
begin
    induction k,
    repeat {rw mul_zero2},
    repeat {rw mul_succ2},
    rw mul_distrib2,
    rw k_ih,
end

theorem mul_comm2: mul m n = mul n m :=
begin
    induction n,
    rw [mul_zero2, zero_mul2],
    rw [mul_succ2, succ_mul2, n_ih, add_comm2],
end

theorem pow_zero2: pow m zero = succ zero :=
begin
    refl,
end

theorem pow_succ2: pow m (succ n) = mul m (pow m n) :=
begin
    refl,
end

theorem zero_pow2: m ≠ zero → pow zero m = zero :=
begin
    intro hmnz,
    induction m,
    contradiction,
    rw [pow_succ2, zero_mul2],
end

theorem pow_add2: pow m (add n k) = mul (pow m n) (pow m k) :=
begin
    induction k,
    rw [add_zero2, pow_zero2, mul_succ2, mul_zero2, add_zero2],
    rw [add_succ2, pow_succ2, pow_succ2, k_ih],
    rw ← mul_assoc2 m (pow m n) (pow m k_n),
    rw mul_comm2 m (pow m n),
    rw mul_assoc2,
end
