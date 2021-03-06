-- vim: ts=2 sw=0 sts=-1 et ai tw=70

-- Natural numbers

-- TODO:
-- shorten the pow theorems
-- work through the sporadic confused comments
-- clean everything up a bit, re naming and formatting
-- try to re-use theorems more

-- stops name conflicts
namespace hidden

inductive mynat
| zero : mynat
| succ (n : mynat) : mynat

namespace mynat

-- this instance stuff is pure voodoo but it seems to make the
-- notation work
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

-- a ^ b should be number of functions from a b-set to an a-set. fight
-- me
def pow: mynat → mynat → mynat
| m 0        := 1
| m (succ n) := m * pow m n

instance: has_pow mynat mynat := ⟨pow⟩

variables {m n k : mynat}

-- ADDITION

-- I'm simping liberally for future reasons
@[simp] theorem add_zero (m : mynat): m + 0 = m := rfl

@[simp]
theorem add_succ (m n : mynat): m + succ n = succ (m + n) := rfl

-- so for some reason all the old code breaks with the new operator
-- instances, so I have to go and replace zero with 0 wherever I used
-- induction. How fix???
@[simp] theorem zz: zero = 0 := rfl

@[simp]
theorem zero_add: ∀ m : mynat, 0 + m = m
| zero     := rfl
| (succ m) := by rw [add_succ, zero_add]

@[simp]
theorem succ_add: ∀ m n : mynat, succ m + n = succ (m + n)
| m zero     := rfl
| m (succ n) := by rw [add_succ, add_succ, succ_add]

theorem add_assoc: ∀ m n k : mynat, (m + n) + k = m + (n + k)
| m n zero     := rfl
| m n (succ k) := by rw [add_succ, add_succ, add_succ, add_assoc]

instance add_is_assoc: is_associative mynat add :=
⟨assume a b c, add_assoc a b c⟩

theorem add_comm: ∀ m n : mynat, m + n = n + m
| m zero     := by rw [zz, add_zero, zero_add]
| m (succ n) := by rw [add_succ, succ_add, add_comm]

instance add_is_comm: is_commutative mynat add :=
⟨assume a b, add_comm a b⟩

@[simp] theorem add_one_succ: m + 1 = succ m := rfl

theorem succ_inj: succ m = succ n → m = n :=
succ.inj

@[simp]
theorem one_eq_succ_zero: succ 0 = 1 := rfl

theorem zero_ne_one : (0:  mynat) ≠ 1 :=
begin
  assume h,
  from mynat.no_confusion h,
end

theorem add_cancel: ∀ {m}, m + n = m + k → n = k
| zero     := by simp; cc
| (succ m) := assume h, by {
  rw [succ_add, succ_add] at h,
  from @add_cancel m (succ_inj h)
}

theorem add_cancel_right: m + n = k + n → m = k :=
begin
  repeat {rw add_comm _ n},
  from add_cancel,
end

-- In the case where nothing is being added on LHS
theorem add_cancel_to_zero: m = m + k → k = 0 :=
begin
  assume hmmk,
  -- use conv to just add zero to the left m
  conv at hmmk { to_lhs, rw ←add_zero m, },
  from add_cancel hmmk.symm,
end

-- again, this is magical cases
theorem succ_ne_zero: succ m ≠ 0 :=
begin
  assume h,
  cases h,
end

theorem nzero_iff_succ: m ≠ 0 ↔ ∃ n, m = succ n :=
begin
  split; assume h, {
    cases m,
      contradiction,
    existsi m,
    refl,
  }, {
    cases h with n h,
    rw h,
    from succ_ne_zero,
  },
end

theorem add_integral: ∀ {m n : mynat}, m + n = 0 → m = 0
| zero     _ := by simp
| (succ m) n :=
begin
  rw succ_add,
  assume h,
  from false.elim (succ_ne_zero h),
end

-- DECIDABILITY

instance: decidable_eq mynat :=
begin
  intros m n,
  induction m with m hm generalizing n, {
    cases n, {
      from is_true rfl,
    }, {
      from is_false succ_ne_zero.symm,
    },
  }, {
    induction n with n hn generalizing m, {
      from is_false succ_ne_zero,
    }, {
      cases (hm n) with hmnen hmeqn, {
        apply is_false,
        assume hsmsn,
        from hmnen (succ_inj hsmsn),
      }, {
        rw hmeqn,
        from is_true rfl,
      },
    },
  },
end

-- MULTIPLICATION

@[simp] theorem mul_zero (m : mynat): m * 0 = 0 := rfl

@[simp]
theorem mul_succ (m n : mynat): m * (succ n) = m + (m * n) := rfl

@[simp] theorem mul_one (m : mynat) : m * 1 = m := rfl

@[simp]
theorem zero_mul: ∀ m : mynat, 0 * m = 0
| zero     := by rw [zz, mul_zero]
| (succ m) := by rw [mul_succ, zero_mul, add_zero]


@[simp]
theorem one_mul: ∀ m : mynat, 1 * m = m
| zero     := by rw [zz, mul_zero]
| (succ m) := by rw [mul_succ, one_mul, add_comm, add_one_succ]

@[simp]
theorem succ_mul: ∀ m n : mynat, (succ m) * n = m * n + n
| m zero     := by rw [zz, mul_zero, mul_zero, add_zero]
| m (succ n) := by conv {
  congr,
    rw [mul_succ, succ_mul, ←add_assoc, ←add_comm (m*n), add_assoc],
  skip,
    rw [mul_succ, add_comm m, add_assoc, add_succ, ←succ_add],
}

@[simp]
theorem mul_add: ∀ m n k : mynat, m * (n + k) = m * n + m * k
| zero     n k := by repeat { rw zz <|> rw zero_mul <|> rw zero_add }
| (succ m) n k := by repeat { rw succ_mul <|> rw mul_add }; ac_refl

theorem mul_assoc: ∀ m n k: mynat, (m * n) * k = m * (n * k)
| m n zero     := by rw [zz, mul_zero, mul_zero, mul_zero]
| m n (succ k) := by rw [mul_succ, mul_succ, mul_add, mul_assoc]

instance mul_is_assoc: is_associative mynat mul :=
⟨assume a b c, mul_assoc a b c⟩

theorem mul_comm: ∀ m n : mynat, m * n = n * m
| m zero     := by rw [zz, mul_zero, zero_mul]
| m (succ n) := by rw [mul_succ, succ_mul, mul_comm, add_comm]

instance mul_is_comm: is_commutative mynat mul :=
⟨assume a b, mul_comm a b⟩

@[simp]
theorem add_mul (m n k : mynat) : (m + n) * k = m * k + n * k :=
by rw [mul_comm (m + n), mul_comm m, mul_comm n, mul_add]

theorem mul_integral: ∀ {m n : mynat}, m ≠ 0 → m * n = 0 → n = 0
| m zero     := by simp
| m (succ n) :=
begin
  assume hmne0 hmn0,
  rw mul_succ at hmn0,
  from false.elim (hmne0 (add_integral hmn0)),
end

theorem mul_integral_symmetric: m * n = 0 → m = 0 ∨ n = 0 :=
begin
  cases m, {
    assume _, left, from rfl,
  }, {
    assume hsmn0,
    right,
    from mul_integral succ_ne_zero hsmn0,
  },
end

theorem mul_cancel: m ≠ 0 → m * n = m * k → n = k :=
begin
  induction n with n hn generalizing m k; assume hmn0 heq, {
    simp at heq,
    symmetry,
    from mul_integral hmn0 heq.symm,
  }, {
    cases k, {
      exfalso,
      rw [zz, mul_zero] at heq,
      from succ_ne_zero (mul_integral hmn0 heq),
    }, {
      rw [mul_succ, mul_succ] at heq,
      rw hn hmn0 (add_cancel heq),
    },
  },
end

theorem mul_cancel_to_one: m ≠ 0 → m = m * k → k = 1 :=
begin
  assume hmn0 hmmk,
  rw [←mul_one m, mul_assoc, one_mul] at hmmk,
  rw mul_cancel hmn0 hmmk,
end

-- POWERS

-- do I really have to spell out mynat like this? yuck
@[simp] theorem pow_zero (m : mynat) : m ^ (0: mynat) = 1 := rfl

@[simp]
theorem pow_succ (m n : mynat) : m ^ (succ n) = m * (m ^ n) := rfl

theorem zero_pow: ∀ {m : mynat}, m ≠ 0 → (0: mynat) ^ m = 0
| zero     := assume h, by contradiction
| (succ m) := assume h, by simp

@[simp]
theorem pow_one: n ^ (1: mynat) = n := rfl

@[simp]
theorem one_pow: ∀ {n : mynat}, (1: mynat) ^ n = 1
| zero     := rfl
| (succ n) := by rw [pow_succ, one_mul, one_pow]

@[simp]
theorem pow_add (m n : mynat) : ∀ k, m ^ (n + k) = (m ^ n) * (m ^ k)
| zero := by simp
| (succ k) := by simp [pow_add]; ac_refl

@[simp]
theorem pow_mul (m n : mynat): ∀ k, (m ^ n) ^ k = m ^ (n * k)
| zero := by rw [zz, pow_zero, mul_zero, pow_zero]
| (succ k) := by rw [pow_succ, mul_succ, pow_add, pow_mul]

@[simp]
theorem mul_pow (m n : mynat): ∀ k : mynat, (m * n) ^ k = m ^ k * n ^ k
| zero := by simp
| (succ k) := by rw [pow_succ, pow_succ, pow_succ, mul_pow]; ac_refl

end mynat

end hidden
