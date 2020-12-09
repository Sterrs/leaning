import .basic
import .add
import ..logic
import ..mynat.le

namespace hidden
namespace myint

open mynat
open myint

variables m n k : myint
variables a b c : mynat

@[simp]
theorem coe_coe_mul : (↑a : myint) * ↑b = ↑(a * b) :=
begin
  repeat { rw coe_nat_def, },
  rw mul_eq_cls rfl rfl,
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp, -- awsome :o
end

theorem mul_comm: m * n = n * m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  repeat {rw mul_eq_cls rfl rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
  split; ac_refl,
end

@[simp]
theorem mul_zero: m * 0 = 0 :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw int_zero,
  repeat {rw mul_eq_cls rfl rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
end

@[simp]
theorem zero_mul : 0 * m = 0 :=
by rw [mul_comm, mul_zero]

@[simp]
theorem mul_one: m * 1 = m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw int_one,
  repeat {rw mul_eq_cls rfl rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
end

@[simp]
theorem one_mul : ∀ {m: myint}, 1 * m = m
:= λ m, by rw [mul_comm, mul_one]

theorem mul_neg_one: m * (-1) = -m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw int_one,
  repeat {rw mul_eq_cls rfl rfl <|> rw neg_eq_cls rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
end

theorem neg_one_mul: ∀ {m : myint}, (-1) * m = -m
:= λ m, by rw [mul_comm, mul_neg_one]

instance mul_is_comm: is_commutative myint mul := ⟨mul_comm⟩

theorem mul_assoc: m * n * k = m * (n * k) :=
begin
  have: ∀ a b: mynat, ∀ f: mynat → mynat, a = b → f a = f b, {
    intros a b f,
    assume hab,
    rw hab,
  },
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  cases quotient.exists_rep k with c hc, subst hc,
  repeat {rw mul_eq_cls rfl rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
  split, { -- ac_refl takes too long without a little kick-start
    repeat {rw mynat.add_assoc <|> rw mynat.mul_assoc},
    apply this,
    ac_refl,
  }, {
    repeat {rw mynat.add_assoc <|> rw mynat.mul_assoc},
    apply this,
    ac_refl,
  },
end

instance mul_is_assoc: is_associative myint mul :=
⟨mul_assoc⟩

theorem mul_neg : m * (-n) = - (m * n) :=
by rw [←mul_neg_one, ←mul_assoc, ←@neg_one_mul (m*n), mul_comm]

theorem neg_mul : (-m) * n = - (m * n) :=
by rw [mul_comm, @mul_comm m, mul_neg]

-- TODO: Stupid name
theorem mul_neg_neg : (-m) * (-n) = m * n :=
by rw [neg_mul, mul_neg, neg_neg]

theorem mul_add : m * (n + k) = m * n + m * k :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  cases quotient.exists_rep k with c hc, subst hc,
  repeat {rw mul_eq_cls rfl rfl <|> rw add_eq_cls rfl rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
  split; ac_refl,
end

theorem add_mul: (m + n) * k = m * k + n * k :=
by rw [mul_comm, @mul_comm m, @mul_comm n, mul_add]

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
  from hsbn0 (mynat.mul_integral hsan0 h),
end

-- it seems likely that these theorems will become easier to prove
-- given some theorems about <.

-- Particularly abs is very dependent on inequalities

-- hmmmmmm
private lemma mul_integral_biased {m n : myint}:
m ≠ 0 → m * n = 0 → n = 0 :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  repeat {rw mul_eq_cls rfl rfl <|> rw int_zero},
  assume haneq0 hab0,
  rw int_pair.sound_exact_iff at hab0,
  rw int_pair.setoid_equiv at hab0,
  simp at hab0,
  repeat {rw int_pair.sound_exact_iff <|> rw int_pair.setoid_equiv},
  simp,
  cases (le_total_order a.a a.b) with ha ha; cases ha with d hd, {
    rw hd at hab0,
    simp at hab0,
    rw ←mynat.add_assoc at hab0,
    rw mynat.add_comm (a.a * b.a) at hab0,
    rw mynat.add_assoc at hab0,
    have := mynat.add_cancel (mynat.add_cancel hab0),
    apply @mynat.mul_cancel d _ _,
    assume hd0,
    apply haneq0,
    apply quotient.sound,
    rw int_pair.setoid_equiv,
    rw hd,
    rw hd0,
    simp,
    symmetry, assumption,
  }, {
    rw hd at hab0,
    simp at hab0,

    conv at hab0 {
      to_rhs,
      rw mynat.add_comm,
    },
    rw mynat.add_assoc at hab0,
    have hw := mynat.add_cancel hab0,
    rw mynat.add_comm at hw,
    have := mynat.add_cancel hw,
    apply @mynat.mul_cancel d _ _,
    assume hd0,
    apply haneq0,
    apply quotient.sound,
    rw int_pair.setoid_equiv,
    rw hd,
    rw hd0,
    simp,
    assumption,
  },
end

theorem mul_integral {m n : myint}:
m * n = 0 → n = 0 ∨ m = 0 :=
begin
  assume hmn,
  by_cases h: m = 0, {
    right, assumption,
  }, {
    left,
    from mul_integral_biased h hmn,
  },
end

theorem mul_nonzero_nonzero : m * n ≠ 0 ↔ m ≠ 0 ∧ n ≠ 0 :=
begin
  split; assume h, {
    have : 0 = (0 : myint) := rfl,
    split, all_goals {
      assume h0,
      subst h0,
    },
    rw zero_mul at h,
    contradiction,
    rw mul_zero at h,
    contradiction,
  }, {
    assume hmn0,
    cases mul_integral hmn0 with hn0 hm0,
      from h.right hn0,
    from h.left hm0,
  },
end

private lemma something_add_one (m : myint): ∃ n, m = n + 1 :=
by existsi (m + (-1)); rw [add_assoc, neg_self_add, add_zero]

private lemma something_sub_one (m : myint): ∃ n, m = n + -1 :=
by existsi (m + 1); rw [add_assoc, self_neg_add, add_zero]

theorem mul_cancel {m n k : myint}: m ≠ 0 → m * n = m * k → n = k :=
begin
  assume hm0 hmnmk,
  have: m * (n - k) = 0, {
    rw sub_def,
    rw mul_add,
    rw hmnmk,
    rw mul_neg,
    simp,
  },
  have this' := mul_integral_biased hm0 this,
  rw ←add_cancel k at this',
  rw sub_def at this',
  rw add_assoc at this',
  simp at this',
  assumption,
end

-- clean up later. These are used in myrat
theorem mul_neg_with : (-m) * n = -(m * n) := neg_mul m n

theorem mul_with_neg : m * (-n) = -(m * n) := mul_neg m n

end myint
end hidden
