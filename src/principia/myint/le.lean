import .basic
import .mul

namespace hidden

namespace myint

open mynat

def le: myint → myint → Prop
| (of_nat a) (of_nat b) := a ≤ b
| (of_nat a) -[1+ b] := false
| -[1+ a] (of_nat b) := true
| -[1+ a] -[1+ b] := b ≤ a

instance: has_le myint := ⟨le⟩

variables {m n k x y z : myint}
variables {a b c : mynat}

@[simp]
theorem nat_nat_le: (↑a:myint) ≤ ↑b ↔ a ≤ b := by trivial

@[simp]
theorem nat_neg_le: ¬(↑a ≤ -[1+ b]) :=
by { rw coe_nat_eq, assume h, from h }

@[simp]
theorem neg_nat_le: -[1+ a] ≤ ↑b := by trivial

@[simp]
theorem neg_neg_le: -[1+ a] ≤ -[1+ b] ↔ b ≤ a := by trivial

instance decidable_le: ∀ m n : myint, decidable (m ≤ n)
| (of_nat a) (of_nat b) :=
by rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_le]; apply_instance
| (of_nat a) -[1+ b] := is_false nat_neg_le
| -[1+ a] (of_nat b) := is_true neg_nat_le
| -[1+ a] -[1+ b] :=
by rw neg_neg_le; apply_instance

theorem le_refl: ∀ {m : myint}, m ≤ m
| (of_nat a) := by rw [←coe_nat_eq, nat_nat_le]; from hidden.le_refl
| -[1+ a] := by rw [neg_neg_le]; from hidden.le_refl

-- Forward implication of definitions being equal
private theorem le_iff_exists_nat_mpr: ∀ {m n : myint},
m ≤ n → ∃ c : mynat, n = m + ↑c
| (of_nat a) (of_nat b) := assume h,
begin
  rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_le] at h,
  cases h with c h,
  existsi c,
  rwa [←coe_nat_eq, ←coe_nat_eq, nat_nat_add, of_nat_cancel],
end
| (of_nat a) -[1+ b] := assume h, by exfalso; from h
| -[1+ a] (of_nat b) := assume h,
by existsi (succ a + b); rw [←nat_nat_add, ←neg_coe_succ, ←add_assoc,
                             neg_self_add, zero_add, coe_nat_eq]
| -[1+ a] -[1+ b] := assume h,
begin
  rw neg_neg_le at h,
  cases h with c h,
  existsi c,
  rw [h, ←neg_coe_succ, ←neg_coe_succ, ←succ_add, ←nat_nat_add,
      neg_distr, add_assoc, neg_self_add, add_zero],
end

-- Reverse implication
private lemma le_add_rhs_coe: ∀ {m n : myint}, m ≤ n → m ≤ n + ↑c
| (of_nat a) (of_nat b) := assume h,
begin
  rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_le] at h,
  rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_add, nat_nat_le],
  apply le_add_rhs,
  assumption,
end
| (of_nat a) -[1+ b] := assume h, by exfalso; from h
| -[1+ a] (of_nat b) := assume h, by rw [←coe_nat_eq, nat_nat_add];
                                     from neg_nat_le
| -[1+ a] -[1+ b] := assume h,
begin
  rw [neg_neg_le] at h,
  cases h with d h,
  rw [h, ←neg_coe_succ, ←neg_coe_succ, ←succ_add, ←nat_nat_add,
      neg_distr],
  sorry,
end

private lemma le_to_add_nat: ∀ {a : mynat}, m ≤ m + ↑a
| zero     := by rw [zz, zero_nat, add_zero]; from le_refl
| (succ a) :=
begin
  rw [←add_one_succ, ←nat_nat_add, ←add_assoc, one_nat],
  apply le_add_rhs_coe,
  from le_to_add_nat,
end

-- Show old defn of ≤ is equivalent (very useful)
theorem le_iff_exists_nat: m ≤ n ↔ ∃ a : mynat, n = m + ↑a :=
begin
  split; assume h, {
    apply le_iff_exists_nat_mpr,
    assumption,
  }, {
    cases h with a ha,
    rw ha,
    apply le_to_add_nat,
  },
end

theorem le_trans: m ≤ n → n ≤ k → m ≤ k :=
begin
  assume hmn hnk,
  rw le_iff_exists_nat at hmn,
  cases hmn with a ha,
  rw le_iff_exists_nat at hnk,
  cases hnk with b hb,
  rw [ha, add_assoc, nat_nat_add] at hb,
  rw le_iff_exists_nat,
  existsi (a+b),
  assumption,
end

theorem le_cancel (k : myint): m ≤ n ↔ m + k ≤ n + k :=
begin
  split; assume h, {
    rw le_iff_exists_nat at h,
    cases h with a h,
    rw [h, add_assoc, @add_comm ↑a, ←add_assoc, le_iff_exists_nat],
    existsi a,
    refl,
  }, {
    rw le_iff_exists_nat at h,
    cases h with a h,
    rw [add_assoc, @add_comm k, ←add_assoc, add_cancel] at h,
    rw le_iff_exists_nat,
    existsi a,
    assumption,
  },
end

theorem le_cancel_to_zero_lhs: m ≤ m + n ↔ 0 ≤ n :=
by rw [←@zero_add m, add_assoc, @add_comm m, ←add_assoc,
       ←le_cancel, zero_add]

-- Exact same proof works :o
theorem le_cancel_to_zero_rhs: m + n ≤ m ↔ n ≤ 0 :=
by rw [←@zero_add m, add_assoc, @add_comm m, ←add_assoc,
       ←le_cancel, zero_add]

theorem le_neg_switch: m ≤ n ↔ -n ≤ -m :=
begin
  split; assume h,{
    rwa [le_cancel n, neg_self_add, le_cancel m, @add_comm (-m),
        add_assoc, neg_self_add, zero_add, add_zero],
  }, {
    rwa [le_cancel n, neg_self_add, le_cancel m, @add_comm (-m),
        add_assoc, neg_self_add, zero_add, add_zero] at h,
  },
end

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
  split; assume h, {
    rw le_iff_exists_nat at h,
    cases h with a h,
    rw [←add_cancel (-↑a), add_assoc, self_neg_add, zero_add,
    add_zero] at h,
    existsi a,
    symmetry, assumption,
  }, {
    cases h with a h,
    rw le_iff_exists_nat,
    existsi a,
    rw [←add_cancel (-↑a), add_assoc, self_neg_add, zero_add,
    add_zero],
    symmetry, assumption,
  },
end

theorem le_comb: m ≤ n → x ≤ y → m + x ≤ n + y :=
begin
  assume hmn hxy,
  rw [le_cancel x, @add_comm n] at hmn,
  rw [le_cancel n, @add_comm y] at hxy,
  from le_trans hmn hxy,
end

-- Here we pretty much require the old definition
theorem le_total_order: ∀ {m n : myint}, m ≤ n ∨ n ≤ m
| (of_nat a) (of_nat b) :=
begin
  cases hidden.le_total_order a b,
    left,
    rwa [←coe_nat_eq, ←coe_nat_eq, nat_nat_le],
  right,
  rwa [←coe_nat_eq, ←coe_nat_eq, nat_nat_le],
end
| (of_nat a) -[1+ b] := by right; from neg_nat_le
| -[1+ a] (of_nat b) := by left; from neg_nat_le
| -[1+ a] -[1+ b] :=
begin
  cases hidden.le_total_order a b,
    right,
    rwa neg_neg_le,
  left,
  rwa neg_neg_le,
end

theorem le_mul_pos: 0 ≤ k → m ≤ n → k * m ≤ k * n :=
begin
  assume h0lek hmn,
  rw zero_le_iff_coe at h0lek,
  cases h0lek with a ha,
  rw le_iff_exists_nat at hmn,
  cases hmn with b hb,
  rw [ha, hb, mul_add, le_cancel_to_zero_lhs, nat_nat_mul],
  apply zero_le_iff_coe.mpr,
  existsi (a*b),
  refl,
end

theorem le_mul_neg: k ≤ 0 → m ≤ n → k * n ≤ k * m :=
begin
  assume hkle0 hmn,
  rw le_zero_iff_neg_coe at hkle0,
  cases hkle0 with a ha,
  rw [ha, neg_mul, neg_mul, le_neg_switch, neg_neg, neg_neg],
  have : 0 ≤ (↑a : myint), {
    rw zero_le_iff_coe,
    existsi a,
    refl,
  },
  from le_mul_pos this hmn,
end

theorem le_antisymm: m ≤ n → n ≤ m → m = n :=
begin
  assume hmn hnm,
  rw le_iff_exists_nat at hmn hnm,
  cases hmn with a ha,
  cases hnm with b hb,
  have hb₁ := hb.symm,
  rw [ha, add_assoc, add_comm, add_cancel_to_zero, nat_nat_add,
      ←zero_nat, of_nat_cancel] at hb₁,
  have := add_integral hb₁,
  rw [this, zero_nat, add_zero] at ha,
  symmetry,
  assumption,
end

theorem square_non_neg: ∀ {m : myint}, 0 ≤ m * m
| (of_nat a) := by rw [←coe_nat_eq, nat_nat_mul, ←zero_nat,
                      nat_nat_le]; from zero_le
| -[1+ a] := by rw [neg_neg_mul, ←zero_nat, nat_nat_le]; from zero_le

end myint
end hidden
