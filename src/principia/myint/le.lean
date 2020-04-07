import .basic
import .add

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

end myint

end hidden
