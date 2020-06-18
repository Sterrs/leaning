-- vim: ts=2 sw=0 sts=-1 et ai tw=70

-- Defining some operations on integers, thought of as pairs of
-- natural numbers (a, b), representing a - b.

-- Modelled heavily after frac from our myrat

import ..logic
import ..mynat.basic
import ..mynat.le
import ..mynat.nat_sub

namespace hidden
open mynat
namespace int_pair

-- the pair (a, b) represents the integer a - b
structure int_pair := (a b: mynat)

instance: has_zero int_pair := ⟨⟨0, 0⟩⟩
instance: has_one int_pair := ⟨⟨1, 0⟩⟩

@[simp] theorem zero_def: (0: int_pair) = ⟨0, 0⟩ := rfl
@[simp] theorem one_def: (1: int_pair) = ⟨1, 0⟩ := rfl

theorem eq_iff_split (n m: int_pair):
n = m ↔ n.a = m.a ∧ n.b = m.b :=
begin
  cases n with na nb,
  cases m with ma mb,
  simp,
end

-- establishing the equivalence relation

def int_pair_eq (n m: int_pair): Prop :=
n.a + m.b = m.a + n.b

theorem int_pair_eq_refl: reflexive int_pair_eq :=
begin
  intro n,
  unfold int_pair_eq,
end

theorem int_pair_eq_symm: symmetric int_pair_eq :=
begin
  intros n m,
  unfold int_pair_eq,
  from eq.symm,
end

theorem int_pair_eq_trans: transitive int_pair_eq :=
begin
  intros n m k,
  unfold int_pair_eq,
  assume hnm hmk,
  apply @mynat.add_cancel _ _ (m.a + m.b),
  conv {
    congr,
    rw mynat.add_assoc,
    congr, skip,
    rw ←mynat.add_assoc,
    congr,
    rw mynat.add_comm,
    rw hnm,
    skip, skip,
    rw mynat.add_assoc,
    congr, skip,
    rw ←mynat.add_assoc,
    congr,
    rw mynat.add_comm,
    rw ←hmk,
  },
  ac_refl,
end

instance int_pair.setoid : setoid int_pair :=
⟨int_pair_eq, ⟨int_pair_eq_refl, int_pair_eq_symm, int_pair_eq_trans⟩⟩

theorem setoid_equiv (x y : int_pair) :
x ≈ y ↔ x.a + y.b = y.a + x.b := iff.rfl

theorem sound_exact_iff (x y: int_pair):
⟦x⟧ = ⟦y⟧ ↔ x ≈ y := iff.intro quotient.exact quotient.sound

instance int_pair_eq_decidable: ∀ n m: int_pair, decidable (n ≈ m) :=
begin
  intros n m,
  rw setoid_equiv,
  from mynat.decidable_eq _ _,
end

-- definitions and definitional equalities

def neg (n: int_pair): int_pair := ⟨n.b, n.a⟩

instance: has_neg int_pair := ⟨neg⟩

@[simp] theorem neg_is_neg {n: int_pair}: neg n = -n := rfl

@[simp] theorem neg_a {n: int_pair}: (-n).a = n.b := rfl
@[simp] theorem neg_b {n: int_pair}: (-n).b = n.a := rfl

theorem neg_well_defined (n m: int_pair):
n ≈ m → ⟦-n⟧ = ⟦-m⟧ :=
begin
  assume hnm,
  apply quotient.sound,
  rw setoid_equiv at *,
  simp,
  rw add_comm,
  rw ←hnm,
  rw add_comm,
end

def add (n m: int_pair): int_pair := ⟨n.a + m.a, n.b + m.b⟩

instance: has_add int_pair := ⟨add⟩

@[simp]
theorem add_add {n m: int_pair}: add n m = n + m := rfl

@[simp] theorem add_a {n m: int_pair}: (n + m).a = n.a + m.a := rfl

@[simp] theorem add_b {n m: int_pair}: (n + m).b = n.b + m.b := rfl

theorem add_well_defined (n m x y: int_pair):
n ≈ x → m ≈ y → ⟦n + m⟧ = ⟦x + y⟧ :=
begin
  assume hnx hmy,
  apply quotient.sound,
  rw setoid_equiv at *,
  simp,
  conv {
    to_lhs,
    rw mynat.add_assoc,
    rw mynat.add_comm m.a,
    rw ←mynat.add_assoc,
    rw ←mynat.add_assoc,
    rw hnx,
    rw mynat.add_assoc,
    rw mynat.add_comm y.b,
    rw hmy,
  },
  ac_refl,
end

def sub (n m: int_pair): int_pair := n + (-m)

instance: has_sub int_pair := ⟨sub⟩

@[simp]
theorem sub_sub (n m: int_pair): sub n m = n - m := rfl

def le (n m: int_pair): Prop := n.a + m.b ≤ m.a + n.b

instance: has_le int_pair := ⟨le⟩

def lt (n m: int_pair): Prop := ¬ m ≤ n

instance: has_lt int_pair := ⟨lt⟩

@[simp]
theorem le_le (n m: int_pair): le n m ↔ n ≤ m := iff.rfl

@[simp]
theorem le_def (n m: int_pair): n ≤ m ↔ n.a + m.b ≤ m.a + n.b
:= iff.rfl

instance decidable_le: ∀ n m: int_pair, decidable (n ≤ m) :=
λ m n, mynat.decidable_le _ _

@[simp]
theorem lt_lt (n m: int_pair): lt n m ↔ n < m := iff.rfl

@[simp]
theorem lt_def (n m: int_pair): n < m ↔ n.a + m.b < m.a + n.b
:= iff.rfl

instance decidable_lt: ∀ n m: int_pair, decidable (n < m) :=
λ n m, not.decidable

private theorem le_well_defined_right (n x m y: int_pair):
n ≈ x → m ≈ y → (n ≤ m → x ≤ y) :=
begin
  assume hnx hmy,
  rw setoid_equiv at *,
  repeat {rw le_def},
  assume hnm,
  apply @mynat.le_cancel _ _ (n.b + m.a),
  conv {
    congr,
    rw mynat.add_assoc,
    rw mynat.add_comm y.b,
    rw mynat.add_assoc,
    rw ←mynat.add_assoc,
    rw ←hnx,
    rw hmy,
  },
  have: n.a + x.b + (y.a + m.b) = n.a + m.b + (y.a + x.b) := by ac_refl,
  rw this, clear this,
  have: y.a + x.b + (n.b + m.a) = m.a + n.b + (y.a + x.b) := by ac_refl,
  rw this,
  apply mynat.le_add,
  assumption,
end

theorem le_well_defined (n m x y: int_pair):
n ≈ x → m ≈ y → ((n ≤ m) = (x ≤ y)) :=
begin
  assume hnx hmy,
  apply propext,
  from iff.intro (le_well_defined_right _ _ _ _ hnx hmy)
                 (le_well_defined_right _ _ _ _ hnx.symm hmy.symm),
end

theorem lt_well_defined (n m x y: int_pair):
n ≈ x → m ≈ y → ((n < m) = (x < y)) :=
begin
  assume hnx hmy,
  have: n < m = ¬m ≤ n := rfl,
  rw this,
  rw le_well_defined m n y x hmy hnx,
  refl,
end

def sign (n: int_pair): int_pair :=
if 0 < n then 1
  else if n < 0 then -1
    else 0

theorem sign_def (n: int_pair):
sign n = if 0 < n then 1
          else if n < 0 then -1
            else 0 := rfl

theorem sign_well_defined (n m: int_pair):
n ≈ m → ⟦sign n⟧ = ⟦sign m⟧ :=
begin
  assume hnm,
  have pos_equiv := lt_well_defined 0 n 0 m (setoid.refl _) hnm,
  have neg_equiv := lt_well_defined n 0 m 0 hnm (setoid.refl _),
  unfold sign,
  by_cases h0n: 0 < n, {
    rw if_pos h0n,
    rw pos_equiv at h0n,
    rw if_pos h0n,
  }, {
    rw if_neg h0n,
    rw pos_equiv at h0n,
    rw if_neg h0n,
    by_cases hn0: n < 0, {
      rw if_pos hn0,
      rw neg_equiv at hn0,
      rw if_pos hn0,
    }, {
      rw if_neg hn0,
      rw neg_equiv at hn0,
      rw if_neg hn0,
    },
  },
end

-- is there an easier way?
private lemma unpropext {p q: Prop}: p = q → (p ↔ q) :=
begin
  assume hpq,
  rw hpq,
end

def mul (n m: int_pair): int_pair := ⟨n.a * m.a + n.b * m.b, n.a * m.b + n.b * m.a⟩

instance: has_mul int_pair := ⟨mul⟩

@[simp]
theorem mul_def {n m: int_pair}: add n m = n + m := rfl

@[simp]
theorem mul_a {n m: int_pair}:
(n * m).a = n.a * m.a + n.b * m.b := rfl

-- one of the lesser known Spice Girls
@[simp]
theorem mul_b {n m: int_pair}:
(n * m).b = n.a * m.b + n.b * m.a := rfl

-- it's very hard to prove multiplication is well defined
-- in both arguments at once
private lemma mul_half_defined (n m x: int_pair):
n ≈ m → ⟦n * x⟧ = ⟦m * x⟧ :=
begin
  assume hnm,
  apply quotient.sound,
  rw setoid_equiv at *,
  simp,
  have:
    n.a * x.a + n.b * x.b + (m.a * x.b + m.b * x.a) =
      (n.a + m.b) * x.a + (n.b  + m.a) * x.b, {
    repeat {rw mul_add <|> rw add_mul},
    ac_refl,
  },
  rw this,
  conv {
    congr,
    congr,
    congr,
    rw hnm,
    skip, skip,
    congr,
    rw add_comm,
    rw ←hnm,
  },
  repeat {rw mul_add <|> rw add_mul},
  ac_refl,
end

theorem mul_comm {n m: int_pair}: n * m = m * n :=
begin
  rw eq_iff_split,
  simp,
  split; ac_refl,
end

theorem mul_well_defined (n m x y: int_pair):
n ≈ x → m ≈ y → ⟦n * m⟧ = ⟦x * y⟧ :=
begin
  assume hnx hmy,
  transitivity ⟦x * m⟧, {
    from mul_half_defined n x m hnx,
  }, {
    repeat {rw @mul_comm x},
    from mul_half_defined m y x hmy,
  },
end

variables {n m k: int_pair}

theorem add_comm: n + m = m + n :=
begin
  rw eq_iff_split,
  simp,
  split; ac_refl,
end

theorem add_assoc: n + m + k = n + (m + k) :=
begin
  rw eq_iff_split,
  simp,
  split; ac_refl,
end

@[simp]
theorem neg_neg: - -n = n :=
begin
  rw eq_iff_split,
  simp,
end

end int_pair
end hidden
