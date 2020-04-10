import .induction
import ..logic

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

theorem one_mul : ∀ {m: myint}, 1 * m = m
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

-- TODO: Stupid name
theorem neg_times_neg : (-m) * (-n) = m * n :=
by rw [neg_mul, mul_neg, neg_neg]

-- Effectively succ_mul for myints
private theorem add_one_mul : ∀ {m n : myint}, (m + 1) * n = m * n + n
| (of_nat a) (of_nat b) :=
by rw [←coe_nat_eq, ←coe_nat_eq, ←one_nat, nat_nat_add, nat_nat_mul,
      nat_nat_mul, nat_nat_add, hidden.add_mul, hidden.one_mul]
| (of_nat a) -[1+ b] :=
by rw [←coe_nat_eq, nat_neg_mul, ←one_nat, nat_nat_add, nat_neg_mul,
       ←neg_cancel, neg_neg, neg_distr, neg_neg, neg_neg_succ,
       nat_nat_add, hidden.add_mul, hidden.one_mul]
| -[1+ a] (of_nat b) :=
by rw [←coe_nat_eq, ←neg_coe_succ, neg_mul, nat_nat_mul, succ_mul,
       ←nat_nat_add, neg_distr, add_assoc, neg_self_add, add_zero,
       ←add_one_succ, ←nat_nat_add, neg_distr, add_assoc, one_nat,
       neg_self_add, add_zero, neg_mul, nat_nat_mul]
| -[1+ a] -[1+ b] := by
  rw [←neg_coe_succ, ←neg_coe_succ, neg_times_neg, mul_neg, ←neg_mul,
      neg_distr, neg_neg, neg_one, nat_neg_add, sub_succ_succ,
      nat_sub_zero, nat_nat_mul, nat_nat_mul, succ_mul, ←nat_nat_add,
      add_assoc, self_neg_add, add_zero]

private theorem sub_one_mul : (m - 1) * n = m * n - n :=
begin
  rw [sub_add_neg, sub_add_neg, ←neg_cancel, ←neg_mul, neg_distr,
      neg_distr, ←neg_mul, neg_neg, neg_neg],
  from add_one_mul,
end

theorem mul_add : m * (n + k) = m * n + m * k :=
begin
  revert m,
  apply intduction, {
    repeat { rw [zero_mul] },
    rw zero_add,
  }, {
    assume m hi,
    rw [add_one_mul, add_one_mul, add_one_mul, hi, add_assoc,
        ←@add_assoc (m*k), @add_comm (m*k), @add_assoc n, ←add_assoc],
  }, {
    assume m hi,
    rw [sub_one_mul, sub_one_mul, sub_one_mul, hi, sub_add_neg,
        neg_distr, sub_add_neg, sub_add_neg, add_assoc,
        ←@add_assoc (m*k), @add_comm (m*k), @add_assoc (-n), ←add_assoc],
  },
end

theorem add_mul: (m + n) * k = m * k + n * k :=
by rw [mul_comm, @mul_comm m, @mul_comm n, mul_add]

private lemma neg_succ_distr: -[1+ a] * m = -m + -(↑a * m) := sorry

theorem nzero_iff_succ_or_neg_succ:
m ≠ 0 ↔ ∃ a, m = ↑(succ a) ∨ m = -↑(succ a) :=
begin
  rw exists_or,
  split; assume h, {
    cases m, {
      left,
      cases m, {
        rw [zz, ←coe_nat_eq, zero_nat] at h,
        contradiction,
      }, {
        existsi m,
        rw ←coe_nat_eq,
      }
    }, {
      right,
      existsi m,
      rw neg_coe_succ,
    },
  }, {
    cases h, {
      cases h with a h,
      assume h0,
      rw [h, ←zero_nat, of_nat_cancel] at h0,
      from mynat.no_confusion h0,
    }, {
      cases h with a h,
      assume h0,
      rw [h, ←neg_zero, ←zero_nat, neg_cancel, of_nat_cancel] at h0,
      from mynat.no_confusion h0,
    },
  },
end

private lemma neq_iff_not_eq: m ≠ n ↔ ¬(m = n) :=
begin
  split; assume hneq heq, all_goals { contradiction },
end

private lemma succ_times_succ_nzero: (succ a) * (succ b) ≠ 0 :=
begin
  assume h,
  have hsan0 : succ a ≠ 0,
    assume h₁,
    from mynat.no_confusion h₁,
  have hsbn0 : succ b ≠ 0,
    assume h₁,
    from mynat.no_confusion h₁,
  from hsbn0 (hidden.mul_integral hsan0 h),
end

--∀ {m n : myint},
theorem mul_integral: m * n = 0 → n = 0 ∨ m = 0 :=
begin
  assume h,
  by_cases (m = 0), {
    right, assumption,
  }, {
    by_cases (n = 0), {
      left, assumption,
    }, {
      rename h hn,
      rename h hm,
      exfalso,
      rw [←neq_iff_not_eq, nzero_iff_succ_or_neg_succ] at hn hm,
      cases hm with a ha,
      cases hn with b hb,
      cases ha; cases hb,
      all_goals { rw [ha, hb] at h }, {
        rw [nat_nat_mul, ←zero_nat, of_nat_cancel] at h,
        from succ_times_succ_nzero h,
      }, {
        rw [mul_neg, nat_nat_mul, ←neg_zero, neg_cancel, ←zero_nat,
            of_nat_cancel] at h,
        from succ_times_succ_nzero h,
      }, {
        rw [neg_mul, nat_nat_mul, ←neg_zero, neg_cancel, ←zero_nat,
            of_nat_cancel] at h,
        from succ_times_succ_nzero h,
      }, {
        rw [neg_times_neg, nat_nat_mul, ←zero_nat, of_nat_cancel] at h,
        from succ_times_succ_nzero h,
      },
    },
  },
end

theorem mul_cancel: m ≠ 0 → m * n = m * k → n = k :=
begin
  assume hmne0 h,
  cases m,
    sorry,
  rw [←neg_coe_succ] at h,
  sorry,
end

end myint
end hidden
