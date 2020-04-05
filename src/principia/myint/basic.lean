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

namespace myint
open myint
open mynat

instance: has_zero myint := ⟨of_nat 0⟩
instance: has_one myint := ⟨of_nat 1⟩

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

def abs : myint → mynat
| (of_nat m) := m
| -[1+ m] := succ m

variables {m n k: myint}
variables {a b c: mynat}

-- Basic

theorem coe_nat_eq (n: mynat): ↑n = of_nat n := rfl

lemma of_nat_zero : of_nat 0 = 0 := rfl

lemma of_nat_one : of_nat 1 = 1 := rfl

theorem zero_nat: (↑(0: mynat): myint) = 0 := rfl

@[simp]
theorem of_nat_inj: (↑a: myint) = ↑b ↔ a = b :=
begin
  split; assume h,
    cases h, refl,
  rw h,
end

@[simp]
theorem neg_succ_of_nat_inj: -[1+ a] = -[1+ b] ↔ a = b :=
begin
  split; assume h,
    cases h, refl,
  congr, assumption,
end

-- Coercion

-- Neg of nat

@[simp]
theorem neg_succ: neg_of_nat (succ a) = -[1+ a] := rfl

-- Sub nat nat

@[simp]
theorem zero_sub_neg: sub_nat_nat 0 a = neg_of_nat a :=
begin
  cases a,
  refl,
  refl,
end

@[simp]
theorem nat_sub_zero: sub_nat_nat a 0 = ↑a :=
begin
  cases a,
    refl,
  refl,
end

@[simp]
theorem sub_succ_succ:
sub_nat_nat (succ a) (succ b) = sub_nat_nat a b :=
begin
  unfold sub_nat_nat,
  rw sub_succ_succ,
  cases (a - b),
  refl,
  refl,
end

-- Neg

-- Abs

end myint
end hidden
