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
| m 0        := m
| m (succ n) := succ (add m n)

instance: has_add mynat := ⟨add⟩

def mul: mynat → mynat → mynat
| m 0        := 0
| m (succ n) := m + mul m n

instance: has_mul mynat := ⟨mul⟩

-- a ^ b should be number of functions from a b-set to an a-set. fight me
def pow: mynat → mynat → mynat
| m 0        := 1
| m (succ n) := m * pow m n

instance: has_pow mynat mynat := ⟨pow⟩

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
  induction m with m_n m_ih, {
    refl
  }, {
    simp,
    assumption,
  },
end

@[simp]
theorem succ_add: succ m + n = succ (m + n) :=
begin
  induction n with n_n n_ih, {
    refl
  }, {
    simp,
    assumption,
  },
end

@[simp]
theorem add_assoc: (m + n) + k = m + (n + k) :=
begin
  induction k with k_n k_ih, {
    refl,
  }, {
    simp,
    assumption,
  },
end

@[simp]
theorem add_comm: m + n = n + m :=
begin
  induction n with n_n n_ih, {
    simp,
  }, {
    simp,
    assumption,
  },
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
  induction m with m_n m_ih, {
    simp,
    cc,
  }, {
    simp,
    repeat {rw add_comm _ m_n},
    assumption,
  },
end

-- In the case where nothing is being added on LHS
theorem add_cancel_to_zero: m = m + k → k = 0 :=
begin
  assume hmmk,
  -- use conv to just add zero to the left m
  conv at hmmk {
    to_lhs,
    rw ←add_zero m,
  },
  symmetry,
  apply add_cancel _ _ _ hmmk,
end

-- again, this is magical cases
theorem succ_ne_zero: succ m ≠ 0 :=
begin
  assume hsm0,
  cases hsm0,
end

theorem add_integral: m + n = 0 → m = 0 :=
begin
  cases m, {
    simp,
  }, {
    simp,
    assume hsmnz,
    exfalso,
    from succ_ne_zero _ hsmnz,
  },
end

@[simp] theorem mul_zero: m * 0 = 0 := rfl

@[simp] theorem mul_succ: m * (succ n) = m + (m * n) := rfl

@[simp] theorem mul_one: m * 1 = m := rfl

@[simp]
theorem zero_mul: 0 * m = 0 :=
begin
  induction m with m_n m_ih, {
    refl
  }, {
    simp,
    assumption,
  },
end

@[simp]
theorem one_mul: 1 * m = m :=
begin
  induction m with m_n m_ih, {
    refl,
  }, {
    simp [m_ih],
  },
end

@[simp]
theorem succ_mul: (succ m) * n = m * n + n :=
begin
  induction n with n_n n_ih, {
    simp,
  }, {
    simp [n_ih],
    rw [←add_assoc, add_comm m n_n, add_assoc],
  },
end

@[simp]
theorem mul_add: m * (n + k) = m * n + m * k :=
begin
  induction m with m_n m_ih, {
    simp,
  }, {
    simp [m_ih],
    conv {
      to_lhs,
      congr,
      skip,
      rw [←add_assoc, add_comm k, add_assoc],
    },
  },
end

@[simp]
theorem mul_assoc: (m * n) * k = m * (n * k) :=
begin
  induction k with k_n k_ih, {
    simp,
  }, {
    simp [k_ih],
  },
end

@[simp]
theorem mul_comm: m * n = n * m :=
begin
  induction n with n_n n_ih, {
    simp,
  }, {
    simp [n_ih],
  },
end

@[simp]
theorem add_mul: (m + n) * k = m * k + n * k :=
begin
  conv {
    to_lhs,
    rw [mul_comm, mul_add],
    congr,
    rw mul_comm, skip,
    rw mul_comm,
  },
end

theorem mul_integral: m ≠ 0 → m * n = 0 → n = 0 :=
begin
  assume hmne0 hmn0,
  cases n, {
    simp,
  }, {
    simp at hmn0,
    have hm0 := add_integral _ _ hmn0,
    contradiction,
  },
end

-- do I really have to spell out mynat like this? yuck
@[simp] theorem pow_zero: m ^ (0: mynat) = 1 := rfl

@[simp] theorem pow_succ: m ^ (succ n) = m * (m ^ n) := rfl

theorem zero_pow: m ≠ 0 → (0: mynat) ^ m = 0 :=
begin
  assume hmn0,
  induction m with m_n m_ih, {
    contradiction,
  }, {
    simp,
  }
end

@[simp]
theorem pow_add: m ^ (n + k) = (m ^ n) * (m ^ k) :=
begin
  induction k with k_n k_ih, {
    simp,
  }, {
    simp [k_ih],
    -- it would be really nice to have a tactic to just
    -- sort out associative commutative operations like this
    conv {
      to_lhs,
      rw ←mul_assoc,
      congr,
      rw mul_comm,
    },
    rw mul_assoc,
  }
end

@[simp]
theorem pow_mul: (m ^ n) ^ k = m ^ (n * k) :=
begin
  induction k with k_n k_ih, {
    simp,
  }, {
    simp [k_ih],
  }
end

@[simp]
theorem mul_pow: (m * n) ^ k = m ^ k * n ^ k :=
begin
  induction k with k_n k_ih, {
    simp,
  }, {
    simp [k_ih],
    conv in (n * _) {
        rw ←mul_assoc,
        congr,
        rw mul_comm,
    },
    rw mul_assoc,
  }
end

end hidden
