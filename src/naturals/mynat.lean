-- Natural numbers

-- TODO:
-- shorten things using other better tactics
-- work through the sporadic confused comments
-- clean everything up a bit, re naming and formatting
-- tidy up the order
-- try to re-use theorems more
-- implement more theorems about more sophisticated arithmetic
-- endgame: perhaps some of the N&S course, maybe an example sheet question?

-- also, I haven't opened classical! Is it really true that none of this
-- requires classical? Let's see how long we can keep it up for

-- stops name conflicts
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

instance: has_pow mynat mynat := ⟨pow⟩

def square (m : mynat) := ∃ k : mynat, m = k*k

variables m n k p: mynat

-- I'm simping liberally for future reasons
@[simp] theorem add_zero: m + 0 = m := rfl

@[simp] theorem add_succ: m + succ n = succ (m + n) := rfl

-- so for some reason all the old code breaks with the new operator instances,
-- so I have to go and replace zero with 0 wherever I used induction. How fix???
@[simp] theorem zz: zero = 0 := rfl

@[simp]
theorem zero_add: 0 + m = m :=
begin
    induction m,
    repeat {rw zz},
    rw add_zero,
    rw [add_succ, m_ih],
end

@[simp]
theorem succ_add: succ m + n = succ (m + n) :=
begin
    induction n,
    refl,
    repeat {rw add_succ},
    rw n_ih,
end

@[simp]
theorem add_assoc: (m + n) + k = m + (n + k) :=
begin
    induction k,
    refl,
    repeat {rw add_succ},
    rw k_ih,
end

@[simp]
theorem add_comm: m + n = n + m :=
begin
    induction n,
    repeat {rw zz},
    rw [add_zero, zero_add],
    rw [add_succ, succ_add, n_ih],
end

@[simp] theorem add_one_succ: m + 1 = succ m := rfl

theorem succ_inj: succ m = succ n → m = n :=
begin
    assume hmn,
    -- jeez this is some magic inductive type stuff
    -- it seems that given a hypothesis of the form
    -- cons₁ x = cons₂ y,
    -- cases can use injectivity to check possible values of x, y
    cases hmn,
    refl,
end

@[simp]
theorem one_eq_succ_zero: succ 0 = 1 := rfl

theorem add_cancel: m + n = m + k → n = k :=
begin
    induction m,
    repeat {rw zz},
    repeat {rw zero_add},
    assume hnk, from hnk,
    repeat {rw succ_add},
    assume hmnmk,
    from m_ih (succ_inj _ _ hmnmk),
end
-- In the case where nothing is being added on LHS
-- This is a bad way to do it
theorem add_cancel_to_zero: m = m + k → k = 0 :=
begin
    assume h,
    rw [←add_zero m, add_assoc, zero_add] at h,
    rw add_cancel m 0 k, assumption,
end

-- no idea
theorem succ_ne_zero: succ m ≠ 0 :=
begin
    cases m,
    repeat {rw zz},
    assume h10,
    cases h10,
    assume hssmz,
    cases hssmz,
end

theorem add_integral: m + n = 0 → m = 0 :=
begin
    cases m,
    repeat {rw zz},
    assume _,
    refl,
    rw succ_add,
    assume hsmnz,
    exfalso,
    from succ_ne_zero _ hsmnz,
end

@[simp] theorem mul_zero: m * 0 = 0 := rfl

@[simp] theorem mul_succ: m * (succ n) = m + (m * n) := rfl

@[simp] theorem mul_one: m * 1 = m := rfl

@[simp]
theorem zero_mul: 0 * m = 0 :=
begin
    induction m,
    refl,
    rw [mul_succ, m_ih, add_zero],
end

@[simp]
theorem one_mul: 1 * m = m :=
begin
    induction m,
    refl,
    rw [mul_succ, m_ih],
    -- try out calc to see how it works
    calc 1 + m_n = succ 0 + m_n   : rfl
             ... = succ (0 + m_n) : by rw succ_add
             ... = succ m_n       : by rw zero_add,
end

@[simp]
theorem succ_mul: (succ m) * n = m * n + n :=
begin
    induction n,
    refl,
    repeat {rw mul_succ},
    rw n_ih,
    rw [add_succ, succ_add, add_assoc],
end

@[simp]
theorem mul_add: m * (n + k) = m * n + m * k :=
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

@[simp]
theorem mul_assoc: (m * n) * k = m * (n * k) :=
begin
    induction k,
    refl,
    repeat {rw mul_succ},
    rw mul_add,
    rw k_ih,
end

@[simp]
theorem mul_comm: m * n = n * m :=
begin
    induction n,
    repeat {rw zz},
    rw [mul_zero, zero_mul],
    rw [mul_succ, succ_mul, n_ih, add_comm],
end

@[simp]
theorem add_mul: (m + n)*k = m*k + n*k :=
begin
    rw mul_comm,
    rw mul_add,
    rw mul_comm m,
    rw mul_comm n,
end

theorem mul_integral: m ≠ 0 → m * n = 0 → n = 0 :=
begin
    assume hmnez hmnz,
    cases n,
    repeat {rw zz},
    rw mul_succ at hmnz,
    exfalso,
    from hmnez (add_integral _ _ hmnz),
end

-- do I really have to spell out mynat like this? yuck
@[simp] theorem pow_zero: m ^ (0: mynat) = 1 := rfl

@[simp] theorem pow_succ: m ^ (succ n) = m * (m ^ n) := rfl

theorem zero_pow: m ≠ 0 → (0: mynat) ^ m = 0 :=
begin
    assume hmnz,
    induction m,
    contradiction,
    rw [pow_succ, zero_mul],
end

@[simp]
theorem pow_add: m ^ (n + k) = (m ^ n) * (m ^ k) :=
begin
    induction k,
    refl,
    rw [add_succ, pow_succ, pow_succ, k_ih],
    rw ←mul_assoc m (m ^ n) (m ^ k_n),
    rw mul_comm m (m ^ n),
    rw mul_assoc,
end

@[simp]
theorem pow_mul: (m ^ n) ^ k = m ^ (n * k) :=
begin
    induction k,
    refl,
    rw [pow_succ, mul_succ, pow_add, k_ih],
end

@[simp]
theorem mul_pow: (m * n) ^ k = m ^ k * n ^ k :=
begin
    induction k,
    refl,
    repeat {rw pow_succ},
    rw k_ih,
    rw ←mul_assoc _ n _,
    rw mul_assoc m _ n,
    rw mul_comm (m ^ k_n) n,
    repeat {rw mul_assoc},
end

end hidden
