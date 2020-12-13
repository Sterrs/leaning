-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..logic
import ..mynat.basic
import ..mynat.le
import ..mynat.nat_sub
import .int_pair
import ..myring.integral_domain

namespace hidden
open mynat

namespace myint
open myint
def myint := quotient int_pair.int_pair.setoid

instance: decidable_eq myint := quotient.decidable_eq

instance: has_coe mynat myint := ⟨λ n, ⟦⟨n, 0⟩⟧⟩

theorem coe_nat_def (a: mynat): (↑a: myint) = ⟦⟨a, 0⟩⟧ := rfl

instance: has_zero myint := ⟨(0: mynat)⟩
instance: has_one myint := ⟨(1: mynat)⟩

theorem int_zero: (0: myint) = ⟦0⟧ := rfl
theorem int_one: (1: myint) = ⟦1⟧ := rfl

theorem coe_zero : ↑(0 : mynat) = (0 : myint) := rfl
theorem coe_one : ↑(1 : mynat) = (1 : myint) := rfl

def neg: myint → myint :=
quotient.lift (λ n, ⟦-n⟧) int_pair.neg_well_defined

instance: has_neg myint := ⟨neg⟩

theorem neg_eq_cls {x: int_pair.int_pair} {n: myint}:
n = ⟦x⟧ → -n = ⟦-x⟧ :=
λ hnx, by rw hnx; refl

def add: myint → myint → myint :=
quotient.lift₂ (λ n m, ⟦n + m⟧) int_pair.add_well_defined

instance: has_add myint := ⟨add⟩

theorem add_eq_cls {x y: int_pair.int_pair} {n m: myint}:
n = ⟦x⟧ → m = ⟦y⟧ → n + m = ⟦x + y⟧ :=
λ hnx hmy, by rw [hnx, hmy]; refl

def sub (n m: myint): myint := n + -m

instance: has_sub myint := ⟨sub⟩

theorem sub_def (n m: myint): n - m = n + -m := rfl

def mul: myint → myint → myint :=
quotient.lift₂ (λ n m, ⟦n * m⟧) int_pair.mul_well_defined

instance: has_mul myint := ⟨mul⟩

theorem mul_eq_cls {x y: int_pair.int_pair} {n m: myint}:
n = ⟦x⟧ → m = ⟦y⟧ → n * m = ⟦x * y⟧ :=
λ hnx hmy, by rw [hnx, hmy]; refl

theorem nat_nat_mul {x y: mynat}:
(↑x: myint) * ↑y = ↑(x * y) :=
begin
  apply quotient.sound,
  rw int_pair.setoid_equiv,
  simp,
end

universe u

-- a decidable relation lifted to a quotient type is decidable
-- This shouldn't be here...
def quotient_decidable_rel
{α : Sort u} {s : setoid α}
(rel: α → α → Prop)
(wd: ∀ n m x y: α, n ≈ x → m ≈ y → (rel n m = rel x y))
[dr : ∀ a b : α, decidable (rel a b)]:
∀ a b: quotient s,
  decidable (quotient.lift₂ rel wd a b) :=
λ q₁ q₂ : quotient s,
  quotient.rec_on_subsingleton₂ q₁ q₂ dr

variables m n k: myint
variables a b c: mynat

lemma of_nat_zero: ↑(0: mynat) = (0: myint) := rfl

lemma of_nat_one: ↑(1: mynat) = (1: myint) := rfl

theorem zero_nat: (↑(0: mynat): myint) = 0 := rfl

theorem one_nat: (↑(1:mynat):myint) = 1 := rfl

@[simp]
theorem of_nat_cancel: (↑a: myint) = ↑b ↔ a = b :=
begin
  repeat {rw coe_nat_def},
  split, {
    assume hab,
    from quotient.exact hab,
  }, {
    assume hab,
    rw hab,
  },
end

@[simp]
theorem coe_succ: (↑(succ a): myint) = ↑a + 1 := rfl

@[simp] theorem coe_coe_add: (↑a: myint) + ↑b = ↑(a + b) := rfl

theorem add_one_succ: (↑a: myint) + 1 = ↑(succ a) := rfl

theorem add_comm: m + n = n + m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  repeat {rw add_eq_cls rfl rfl},
  -- honestly this just happened to work
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
  split; ac_refl,
end

instance add_is_comm: is_commutative myint add :=
⟨myint.add_comm⟩

theorem add_zero: m + 0 = m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw int_zero,
  rw add_eq_cls rfl rfl,
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
end

theorem add_assoc: m + n + k = m + (n + k) :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  cases quotient.exists_rep k with c hc, subst hc,
  repeat {rw add_eq_cls rfl rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
  split; ac_refl,
end

instance add_is_assoc: is_associative myint add :=
⟨add_assoc⟩

theorem add_neg: m + (-m) = 0 :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw int_zero,
  rw neg_eq_cls rfl,
  rw add_eq_cls rfl rfl,
  apply quotient.sound,
  rw int_pair.setoid_equiv,
  simp,
  rw mynat.add_comm,
end

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
theorem mul_one: m * 1 = m :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  rw int_one,
  repeat {rw mul_eq_cls rfl rfl},
  apply congr rfl,
  rw int_pair.eq_iff_split,
  simp,
end

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

-- theorem mul_nonzero_nonzero : m * n ≠ 0 ↔ m ≠ 0 ∧ n ≠ 0 :=
-- begin
--   split; assume h, {
--     have : 0 = (0 : myint) := rfl,
--     split, all_goals {
--       assume h0,
--       subst h0,
--     },
--     rw zero_mul at h,
--     contradiction,
--     rw mul_zero at h,
--     contradiction,
--   }, {
--     assume hmn0,
--     cases mul_integral hmn0 with hn0 hm0,
--       from h.right hn0,
--     from h.left hm0,
--   },
-- end

-- private lemma something_add_one (m : myint): ∃ n, m = n + 1 :=
-- by existsi (m + (-1)); rw [add_assoc, neg_self_add, add_zero]

-- private lemma something_sub_one (m : myint): ∃ n, m = n + -1 :=
-- by existsi (m + 1); rw [add_assoc, self_neg_add, add_zero]

instance: myring myint :=
⟨add_assoc, add_zero, add_neg, mul_assoc, mul_comm, mul_one, mul_add⟩

instance: integral_domain myint := ⟨begin
  intros a b ha h,
  apply mul_integral_biased ha,
  rwa myring.mul_comm,
end⟩

end myint
end hidden
