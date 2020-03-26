import principia.mynat
import principia.le

namespace hidden

-- Basic definitions for integers
-- TODO:
-- - Prove basic theorems about arithmetic again
-- - Probably move aux_sub_nat_nat into mynat and prove some things about it
--   there
-- - Define some quotient/remainder things

inductive myint: Type
| of_nat          : mynat → myint
| neg_succ_of_nat : mynat → myint

-- "has coercion" I think. Seems to introduce the notation
-- ↑n (\u n) for "coerce n"
instance: has_coe mynat myint := ⟨myint.of_nat⟩

-- lets you write -[1+ n] for negative numbers. Note the spacing is unforgiving
notation `-[1+ ` n `]` := myint.neg_succ_of_nat n

-- I don't really know how namespace work in lean tbh
namespace myint
open myint
open mynat (succ)

theorem coe_nat_eq (n: mynat): ↑n = of_nat n := rfl

instance: has_zero myint := ⟨of_nat 0⟩
instance: has_one myint := ⟨of_nat 1⟩

lemma of_nat_zero : of_nat 0 = 0 := rfl

lemma of_nat_one : of_nat 1 = 1 := rfl

def neg_of_nat: mynat → myint
| 0        := 0
| (succ m) := -[1+ m]

def aux_sub_nat_nat: mynat → mynat → mynat
| m 0               := m
| 0 n               := 0
| (succ m) (succ n) := aux_sub_nat_nat m n

def sub_nat_nat (m n: mynat): myint :=
match aux_sub_nat_nat m n with
| 0 := of_nat (aux_sub_nat_nat n m)
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

variables m n k : myint

def add_assoc : (m + n) + k = m + (n + k) :=
begin
  sorry,
end

end myint
end hidden
