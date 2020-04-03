-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..mynat.basic
import ..mynat.le
import ..mynat.nat_sub

namespace hidden

-- Basic definitions for integers
-- TODO:
-- - Prove basic theorems about arithmetic again
-- - Define some quotient/remainder things

inductive myint: Type
| of_nat         : mynat → myint
| neg_succ_of_nat: mynat → myint

-- "has coercion" I think. Seems to introduce the notation
-- ↑n (\u n) for "coerce n"
instance: has_coe mynat myint := ⟨myint.of_nat⟩

-- lets you write -[1+ n] for negative numbers. Note the spacing is
-- unforgiving.
notation `-[1+ ` n `]` := myint.neg_succ_of_nat n

-- I don't really know how namespace work in lean tbh
namespace myint
open myint
open mynat

theorem coe_nat_eq (n: mynat): ↑n = of_nat n := rfl

instance: has_zero myint := ⟨of_nat 0⟩
instance: has_one myint := ⟨of_nat 1⟩

lemma of_nat_zero : of_nat 0 = 0 := rfl

lemma of_nat_one : of_nat 1 = 1 := rfl

def neg_of_nat: mynat → myint
| 0        := 0
| (succ m) := -[1+ m]

def sub_nat_nat (m n: mynat): myint :=
match m - n with
| 0 := neg_of_nat (n - m)
| d := d
end

def neg: myint → myint
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

instance: has_neg myint := ⟨neg⟩

def add: myint → myint → myint
| (of_nat m) (of_nat n) := of_nat (m + n)
| -[1+ m] (of_nat n)    := sub_nat_nat n (succ m)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m] -[1+ n]       := -[1+ succ (m + n)]

instance: has_add myint := ⟨add⟩

def mul: myint → myint → myint
| (of_nat m) (of_nat n) := of_nat (m * n)
| -[1+ m] (of_nat n)    := neg_of_nat (succ m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m] -[1+ n]       := of_nat (succ m * succ n)

instance: has_mul myint := ⟨mul⟩

-- maybe this is done automatically anyway, idk
def sub (m n: myint): myint := m + (-n)
instance: has_sub myint := ⟨sub⟩

def abs : myint → mynat
| (of_nat m) := m
| -[1+ m] := succ m

variables {m n k: myint}
variables {m' n' k': mynat}

-- ADDITION

@[simp] theorem nat_nat_add: (↑m': myint) + ↑n' = ↑(m' + n') := rfl

@[simp]
theorem neg_nat_add: -[1+ m'] + ↑n' = sub_nat_nat n' (succ m') := rfl

@[simp]
theorem nat_neg_add: ↑m' + -[1+ n'] = sub_nat_nat m' (succ n') := rfl

@[simp]
theorem neg_neg_add: -[1+ m'] + -[1+ n'] = -[1+ succ (m' + n')] := rfl


@[simp] theorem of_nat_coe: of_nat m' = ↑m' := rfl
@[simp] theorem of_nat_inj: (↑m': myint) = ↑n' ↔ m' = n' :=
begin
  split,
  assume h, cases h, refl,
  assume h, rw h,
end

theorem zero_nat: (↑(0: mynat): myint) = 0 := rfl

theorem of_nat_succ_add_one: of_nat (succ m') = of_nat m' + 1 := rfl

@[simp]
theorem add_comm: m + n = n + m :=
begin
  cases m,
  cases n,
  simp,
  simp,
  cases n,
  simp,
  simp,
end

@[simp]
theorem zero_sub_neg: sub_nat_nat 0 m' = neg_of_nat m' :=
begin
  cases m',
  refl,
  refl,
end

@[simp]
theorem neg_succ: neg_of_nat (succ m') = -[1+ m'] := rfl

@[simp]
theorem zero_add: 0 + m = m :=
begin
  cases m,
  rw ←zero_nat,
  simp,
  rw ←zero_nat,
  simp,
end

@[simp]
theorem add_zero: m + 0 = m :=
begin
  have := @zero_add m,
  rwa add_comm,
end

@[simp]
theorem nat_sub_zero: sub_nat_nat m' 0 = ↑m' :=
begin
  cases m',
  refl,
  refl,
end

@[simp]
theorem sub_succ_succ:
sub_nat_nat (succ m') (succ n') = sub_nat_nat m' n' :=
begin
  unfold sub_nat_nat,
  rw sub_succ_succ,
  cases (m' - n'),
  refl,
  refl,
end

@[simp]
theorem succ_of_sub_succ:
sub_nat_nat m' (succ n') + 1 = sub_nat_nat m' n' :=
begin
  cases m',
    simp,
    sorry,
  rw sub_succ_succ,
  sorry,
end

@[simp]
theorem sub_nat_succ:
sub_nat_nat (succ m') n' = sub_nat_nat m' n' + 1 :=
begin
  induction n' with n'_n n'_ih,
  simp,
  rw add_comm,
  refl,
  simp,
end

@[simp]
theorem coe_succ: (↑(succ m'): myint) = ↑m' + 1 := rfl

@[simp]
theorem sub_nat_add:
sub_nat_nat (m' + n') k' = m' + sub_nat_nat n' k' :=
begin
  induction m' with m'_n m'_ih,
  simp,
  rw zero_nat,
  simp,
  rw [succ_add, sub_nat_succ, m'_ih],
  sorry,
end

theorem add_congr (k : myint) : m = n → m + k = n + k := sorry

theorem add_cancel (k : myint) : m + k = n + k → m = n := sorry

theorem add_self_neg : m + (-m) = 0 := sorry

theorem add_neg_self : -m + m = 0 := sorry

theorem add_assoc : m + n + k = m + (n + k) := sorry

-- MULTIPLICATION

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
