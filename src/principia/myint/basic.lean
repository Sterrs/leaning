-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..logic
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

def sign : myint → myint
| (of_nat a) :=
match a with
| zero     := 0
| (succ _) := 1
end
| -[1+ _] := -1

variables {m n k: myint}
variables {a b c: mynat}

-- Basic

lemma of_nat_zero : of_nat 0 = 0 := rfl

lemma of_nat_one : of_nat 1 = 1 := rfl

theorem zero_nat: (↑(0: mynat): myint) = 0 := rfl

theorem one_nat: (↑(1:mynat):myint) = 1 := rfl

theorem neg_one: -(1:myint) = -[1+ 0] := rfl

theorem of_nat_ne_neg_succ: of_nat a ≠ -[1+ b] := by
  apply myint.no_confusion

theorem zero_ne_neg_succ (a : mynat): 0 ≠ -[1+ a] := by
  apply of_nat_ne_neg_succ

@[simp]
theorem of_nat_cancel: (↑a: myint) = ↑b ↔ a = b :=
begin
  split; assume h,
    cases h, refl,
  rw h,
end

@[simp]
theorem neg_succ_of_nat_cancel: -[1+ a] = -[1+ b] ↔ a = b :=
begin
  split; assume h,
    cases h, refl,
  congr, assumption,
end

-- Coercion

@[simp]
theorem coe_nat_eq (n: mynat): ↑n = of_nat n := rfl

-- Neg of nat

@[simp]
theorem neg_of_nat_zero: neg_of_nat 0 = 0 := rfl

@[simp]
theorem neg_succ: neg_of_nat (succ a) = -[1+ a] := rfl

-- Massive cash bash, for very basic theorem
@[simp]
theorem neg_of_nat_cancel: ∀ {a b}, neg_of_nat a = neg_of_nat b ↔ a = b :=
begin
  assume a b,
  split; assume h,
    cases a,
      cases b, refl,
      rw zz,
      rw [zz, neg_of_nat_zero, neg_succ] at h,
      exfalso,
      from zero_ne_neg_succ b h,
    cases b,
      rw [zz, neg_succ, neg_of_nat_zero] at h,
      exfalso, from zero_ne_neg_succ a h.symm,
    congr,
    rw [neg_succ, neg_succ] at h,
    rw ←neg_succ_of_nat_cancel,
    assumption,
  congr,
  assumption,
end

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

-- Extremely useful
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

@[simp]
theorem sub_self: ∀ a, sub_nat_nat a a = 0
| zero := rfl
| (succ a) := by rw [sub_succ_succ, sub_self]

-- Neg

lemma neg_eq_minus: neg m = -m := rfl

theorem neg_coe_eq_neg_of_nat: -(↑a) = neg_of_nat a := rfl

private theorem neg_neg_of_nat: ∀ {a}, -neg_of_nat a = ↑a
| zero     := rfl
| (succ a) := rfl

theorem neg_zero: -(0:myint) = 0 := rfl

theorem neg_neg_succ: -(-[1+ a]) = ↑(succ a) := by
rw ←neg_eq_minus; refl

theorem neg_coe_succ: -(↑(succ a)) = -[1+ a] := rfl

theorem neg_neg: ∀ {m : myint}, -(-m) = m
| (of_nat a) := by rw [←coe_nat_eq, neg_coe_eq_neg_of_nat];
                   from neg_neg_of_nat
| -[1+ a]    := by rw neg_neg_succ; refl

theorem neg_switch: -m = n → m = -n :=
begin
  assume h,
  -- To "do the same to both sides"
  have h₁ := congr_arg (λ m, -m) h,
  simp at h₁, -- To simp lambdas
  rwa neg_neg at h₁,
end

theorem neg_cancel: -m = -n ↔ m = n :=
begin
  repeat {rw ←neg_eq_minus},
  split; assume h,
    repeat {rw neg_eq_minus at h},
    have h₁ := congr_arg (λ m, -m) h,
    simp at h₁,
    repeat {rw neg_neg at h₁},
    assumption,
  congr, assumption,
end

theorem sub_nat_nat_switch: ∀ {a b : mynat},
-(sub_nat_nat a b) = sub_nat_nat b a
| zero zero := rfl
| zero (succ b) := rfl
| (succ a) zero := rfl
| (succ a) (succ b) :=
by rw [sub_succ_succ, sub_succ_succ, sub_nat_nat_switch]

-- Abs

theorem abs_of_nat: abs ↑a = a := rfl

theorem abs_neg_succ: abs -[1+ a] = succ a := rfl

theorem abs_neg: ∀ {m}, abs (-m) = abs m
| (of_nat a) :=
begin
  rw ←coe_nat_eq,
  cases a, {
    rw [zz, zero_nat, neg_zero],
  }, {
    rw [←neg_neg_succ, neg_neg, neg_neg_succ, abs_of_nat,
        abs_neg_succ],
  },
end
| -[1+ a] :=
by rw [neg_neg_succ, abs_neg_succ, abs_of_nat]

-- Sign

theorem sign_zero: sign 0 = 0 := rfl

theorem sign_neg_succ: sign -[1+ a] = -1 := rfl

theorem sign_succ: sign ↑(succ a) = 1 := rfl

theorem zero_iff_sign_zero: m = 0 ↔ sign m = 0 :=
begin
  split; assume h, {
    subst h, refl,
  }, {
    sorry,
  },
end

theorem nzero_iff_sign_nzero: m ≠ 0 ↔ sign m ≠ 0 :=
iff_to_contrapositive zero_iff_sign_zero

-- Decidability

instance: decidable_eq myint
| (of_nat a) (of_nat b) :=
by rw [←coe_nat_eq, ←coe_nat_eq, of_nat_cancel]; apply_instance
| (of_nat a) -[1+ b] := is_false of_nat_ne_neg_succ
| -[1+ a] (of_nat b) := is_false of_nat_ne_neg_succ.symm
| -[1+ a] -[1+ b] := by rw [neg_succ_of_nat_cancel]; apply_instance

end myint
end hidden
