import .basic
import .int_pair

import ..mynat.sum
import ..myring.order

namespace hidden

namespace myint

open myring
open ordered_myring

def le: myint → myint → Prop :=
quotient.lift₂ int_pair.le int_pair.le_well_defined

instance: has_le myint := ⟨le⟩

theorem le_eq_cls {x y: int_pair.int_pair} {n m: myint}:
n = ⟦x⟧ → m = ⟦y⟧ → (n ≤ m ↔ x ≤ y) :=
λ hnx hmy, by rw [hnx, hmy]; refl

variables m n k x y z : myint
variables a b c : mynat

@[simp]
theorem coe_coe_le: (↑a:myint) ≤ ↑b ↔ a ≤ b := iff.rfl

instance decidable_le: ∀ m n : myint, decidable (m ≤ n) :=
quotient_decidable_rel int_pair.le int_pair.le_well_defined

-- theorems leading up to ordered ring instance proof

-- is this somewhere else?
theorem coe_inj {m n: mynat}: (↑m: myint) = ↑n → m = n :=
begin
  assume hmn,
  have := quotient.exact hmn,
  cases this,
  refl,
end

lemma le_add_rhs_coe {m n : myint}: m ≤ n → m ≤ n + ↑c :=
begin
  assume hmn,
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  rw coe_nat_def,
  rw add_eq_cls rfl rfl,
  rw le_eq_cls rfl rfl,
  rw le_eq_cls rfl rfl at hmn,
  rw int_pair.le_def at *,
  simp,
  have: b.a + c + a.b = b.a + a.b + c := by ac_refl,
  rw this,
  from mynat.le_add_rhs hmn,
end

-- Show old defn of ≤ is equivalent (very useful)
theorem le_iff_exists_nat: m ≤ n ↔ ∃ a : mynat, n = m + ↑a :=
begin
  split, {
    assume hmn,
    cases quotient.exists_rep m with a ha, subst ha,
    cases quotient.exists_rep n with b hb, subst hb,
    rw le_eq_cls rfl rfl at hmn,
    cases hmn with d hd,
    existsi d,
    rw coe_nat_def,
    rw add_eq_cls rfl rfl,
    apply quotient.sound,
    rw int_pair.setoid_equiv,
    simp,
    rw hd,
    ac_refl,
  }, {
    assume h,
    cases h with a ha,
    subst ha,
    apply le_add_rhs_coe,
    cases quotient.exists_rep m with a ha, subst ha,
    from mynat.le_refl,
  },
end

instance: ordered_myring myint := ⟨
  λ a b c: myint,
  begin
    cases quotient.exists_rep a with n hn, subst hn,
    cases quotient.exists_rep b with m hm, subst hm,
    cases quotient.exists_rep c with k hk, subst hk,
    repeat {rw add_eq_cls rfl rfl},
    repeat {rw le_eq_cls rfl rfl},
    repeat {rw int_pair.le_def},
    repeat {rw int_pair.add_a <|> rw int_pair.add_b},
    rw (by ac_refl: n.a + k.a + (m.b + k.b) = n.a + m.b + (k.a + k.b)),
    rw (by ac_refl: m.a + k.a + (n.b + k.b) = m.a + n.b + (k.a + k.b)),
    apply mynat.le_add,
  end,
  begin
    intros a b,
    assume h0a h0b,
    cases (le_iff_exists_nat _ _).mp h0a with n hn,
    cases (le_iff_exists_nat _ _).mp h0b with m hm,
    rw le_iff_exists_nat,
    existsi n * m,
    rw hn,
    rw hm,
    repeat {rw zero_add},
    rw coe_coe_mul,
  end,
  begin
    intros a b c,
    repeat {rw le_iff_exists_nat},
    assume hab, cases hab with n hn,
    assume hbc, cases hbc with m hm,
    existsi n + m,
    rw hm,
    rw hn,
    rw add_assoc,
    rw coe_coe_add,
  end,
  begin
    intros a b,
    cases quotient.exists_rep a with n hn, subst hn,
    cases quotient.exists_rep b with m hm, subst hm,
    from mynat.le_total_order _ _,
  end,
  begin
    intros a b,
    assume hab hba,
    cases (le_iff_exists_nat _ _).mp hab with n hn,
    cases (le_iff_exists_nat _ _).mp hba with m hm,
    rw hn at hm,
    rw add_assoc at hm,
    have hnm0 := add_cancel_right_to_zero _ _ hm.symm,
    rw coe_coe_add at hnm0,
    rw ←coe_zero at hnm0,
    have := coe_inj hnm0,
    rw mynat.add_integral this at hn,
    rw hn,
    symmetry,
    from add_zero _,
  end⟩

-- nonsense theorems that probably aren't used anywhere else

theorem zero_le_iff_coe: 0 ≤ m ↔ ∃ a: mynat, m = ↑a :=
begin
  split; assume h, {
    rw le_iff_exists_nat at h,
    cases h with a h,
    rw zero_add at h,
    existsi a,
    assumption,
  }, {
    rw le_iff_exists_nat,
    cases h with a h,
    existsi a,
    rwa zero_add,
  },
end

theorem le_zero_iff_neg_coe: m ≤ 0 ↔ ∃ a : mynat, m = -↑a :=
begin
  rw le_neg_switch_iff,
  rw neg_zero,
  -- can't rewrite inside a ∃
  split, {
    assume h0m,
    cases (zero_le_iff_coe _).mp h0m with a ha,
    existsi a,
    rw ←ha,
    rw neg_neg,
  }, {
    assume hex,
    apply (zero_le_iff_coe _).mpr,
    cases hex with a ha,
    existsi a,
    rw ha,
    rw neg_neg,
  },
end

-- add this to myring
theorem le_sqrt_nonneg {m n : myint} (hm : 0 ≤ m) (hn : 0 ≤ n) :
m ≤ n ↔ m * m ≤ n * n :=
begin
  split; assume h, {
    apply le_mul_comb_nonneg; assumption,
  }, {
    -- Should be possible to convert to coercion and then use mynat.le_sqrt
    rw zero_le_iff_coe at hm,
    rw zero_le_iff_coe at hn,
    cases hm with a ha, subst ha,
    cases hn with b hb, subst hb,
    rw coe_coe_le,
    repeat {rw coe_coe_mul at h},
    rw coe_coe_le at h,
    apply mynat.le_sqrt,
    assumption,
  },
end

end myint
end hidden
