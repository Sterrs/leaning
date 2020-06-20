-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..logic
import ..mynat.basic
import ..mynat.le
import ..mynat.nat_sub
import .int_pair

namespace hidden
open mynat

namespace quotint
open quotint
def quotint := quotient int_pair.int_pair.setoid

instance: decidable_eq quotint := quotient.decidable_eq

instance: has_coe mynat quotint := ⟨λ n, ⟦⟨n, 0⟩⟧⟩

theorem coe_nat_def (a: mynat): (↑a: quotint) = ⟦⟨a, 0⟩⟧ := rfl

def neg_succ_of_nat (n: mynat): quotint := ⟦⟨0, succ n⟩⟧

-- should probably be phased out of use
notation `-[1+ ` n `]` := neg_succ_of_nat n

theorem neg_succ_def (a: mynat): -[1+ a] = ⟦⟨0, succ a⟩⟧ := rfl

instance: has_zero quotint := ⟨(0: mynat)⟩
instance: has_one quotint := ⟨(1: mynat)⟩

theorem int_zero: (0: quotint) = ⟦0⟧ := rfl
theorem int_one: (1: quotint) = ⟦1⟧ := rfl

theorem coe_zero : ↑(0 : mynat) = (0 : quotint) := rfl
theorem coe_one : ↑(1 : mynat) = (1 : quotint) := rfl

def neg: quotint → quotint :=
quotient.lift (λ n, ⟦-n⟧) int_pair.neg_well_defined

instance: has_neg quotint := ⟨neg⟩

theorem neg_eq_cls {x: int_pair.int_pair} {n: quotint}:
n = ⟦x⟧ → -n = ⟦-x⟧ :=
λ hnx, by rw hnx; refl

def sign: quotint → quotint :=
quotient.lift (λ n, ⟦int_pair.sign n⟧) int_pair.sign_well_defined

theorem sign_eq_cls {x: int_pair.int_pair} {n: quotint}:
n = ⟦x⟧ → sign n = ⟦int_pair.sign x⟧ :=
λ hnx, by rw hnx; refl

def add: quotint → quotint → quotint :=
quotient.lift₂ (λ n m, ⟦n + m⟧) int_pair.add_well_defined

instance: has_add quotint := ⟨add⟩

theorem add_eq_cls {x y: int_pair.int_pair} {n m: quotint}:
n = ⟦x⟧ → m = ⟦y⟧ → n + m = ⟦x + y⟧ :=
λ hnx hmy, by rw [hnx, hmy]; refl

def sub (n m: quotint): quotint := n + -m

instance: has_sub quotint := ⟨sub⟩

theorem sub_def (n m: quotint): n - m = n + -m := rfl

def mul: quotint → quotint → quotint :=
quotient.lift₂ (λ n m, ⟦n * m⟧) int_pair.mul_well_defined

instance: has_mul quotint := ⟨mul⟩

theorem mul_eq_cls {x y: int_pair.int_pair} {n m: quotint}:
n = ⟦x⟧ → m = ⟦y⟧ → n * m = ⟦x * y⟧ :=
λ hnx hmy, by rw [hnx, hmy]; refl

theorem nat_nat_mul {x y: mynat}:
(↑x: quotint) * ↑y = ↑(x * y) :=
begin
  apply quotient.sound,
  rw int_pair.setoid_equiv,
  simp,
end

def le: quotint → quotint → Prop :=
quotient.lift₂ int_pair.le int_pair.le_well_defined

instance: has_le quotint := ⟨le⟩

theorem le_eq_cls {x y: int_pair.int_pair} {n m: quotint}:
n = ⟦x⟧ → m = ⟦y⟧ → (n ≤ m ↔ x ≤ y) :=
λ hnx hmy, by rw [hnx, hmy]; refl

def lt: quotint → quotint → Prop :=
quotient.lift₂ int_pair.lt int_pair.lt_well_defined

instance: has_lt quotint := ⟨lt⟩

theorem lt_eq_cls {x y: int_pair.int_pair} {n m: quotint}:
n = ⟦x⟧ → m = ⟦y⟧ → (n < m ↔ x < y) :=
λ hnx hmy, by rw [hnx, hmy]; refl

universe u

-- a decidable relation lifted to a quotient type is decidable
def quotient_decidable_rel
{α : Sort u} {s : setoid α}
(rel: α → α → Prop)
(wd: ∀ n m x y: α, n ≈ x → m ≈ y → (rel n m = rel x y))
[dr : ∀ a b : α, decidable (rel a b)]:
∀ a b: quotient s,
  decidable (quotient.lift₂ rel wd a b) :=
λ q₁ q₂ : quotient s,
  quotient.rec_on_subsingleton₂ q₁ q₂ dr

variables {m n k: quotint}
variables {a b c: mynat}

lemma of_nat_zero: ↑(0: mynat) = (0: quotint) := rfl

lemma of_nat_one: ↑(1: mynat) = (1: quotint) := rfl

theorem zero_nat: (↑(0: mynat): quotint) = 0 := rfl

theorem one_nat: (↑(1:mynat):quotint) = 1 := rfl

theorem neg_one: -(1:quotint) = -[1+ 0] := rfl

theorem of_nat_ne_neg_succ: ↑a ≠ -[1+ b] :=
begin
  assume haminb,
  rw coe_nat_def at haminb,
  rw neg_succ_def at haminb,
  from succ_ne_zero (quotient.exact haminb),
end

theorem zero_ne_neg_succ (a : mynat): 0 ≠ -[1+ a] := by
  apply of_nat_ne_neg_succ

@[simp]
theorem of_nat_cancel: (↑a: quotint) = ↑b ↔ a = b :=
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

theorem neg_succ_of_nat_cancel: -[1+ a] = -[1+ b] ↔ a = b :=
begin
  repeat {rw coe_nat_def},
  split, {
    assume hab,
    symmetry,
    have := quotient.exact hab,
    rw int_pair.setoid_equiv at this,
    simp at this,
    assumption,
  }, {
    assume hab,
    rw hab,
  },
end

@[simp]
theorem neg_neg: - -n = n :=
begin
  cases (quotient.exists_rep n) with x hx, subst hx,
  repeat {rw neg_eq_cls rfl},
  rw int_pair.neg_neg,
end

theorem neg_cancel: n = m ↔ -n = -m :=
begin
  split, {
    assume hnm, rw hnm,
  }, {
    assume hnm,
    suffices h: - -n = - -m, {
      simp at h,
      assumption,
    }, {
      rw hnm,
    },
  },
end

@[simp]
theorem sub_self: n - n = 0 :=
begin
  cases (quotient.exists_rep n) with x hx, subst hx,
  rw sub_def,
  rw neg_eq_cls rfl,
  rw add_eq_cls rfl rfl,
  apply quotient.sound,
  rw int_pair.setoid_equiv,
  simp,
  rw mynat.add_comm,
end

@[simp]
theorem neg_zero: -(0:quotint) = 0 := rfl

theorem neg_switch: -m = n → m = -n :=
begin
  assume h,
  -- To "do the same to both sides"
  have h₁ := congr_arg (λ m, -m) h,
  simp at h₁, -- To simp lambdas
  assumption,
end

-- Sign

theorem sign_zero: sign 0 = 0 := rfl

theorem sign_neg_succ: sign -[1+ a] = -1 :=
begin
  sorry,
end

-- °_° wtf
theorem sign_succ: sign ↑(succ a) = 1 := rfl

theorem zero_iff_sign_zero: m = 0 ↔ sign m = 0 :=
begin
  split; assume h, {
    subst h, refl,
  }, {
    sorry,
    -- cases m, {
    --   cases m, {
    --     rw [zz, ←coe_nat_eq, zero_nat],
    --   }, {
    --     exfalso,
    --     rw [←coe_nat_eq, sign_succ, ←zero_nat, ←one_nat, of_nat_cancel]
    --     at h,
    --     from mynat.no_confusion h,
    --   },
    -- }, {
    --   exfalso,
    --   rw [sign_neg_succ] at h,
    --   from quotint.no_confusion h,
    -- },
  },
end

theorem sign_mult : sign (m * n) = sign m * sign n := sorry

theorem nzero_iff_sign_nzero: m ≠ 0 ↔ sign m ≠ 0 :=
iff_to_contrapositive zero_iff_sign_zero

theorem zero_ne_one : (0 : quotint) ≠ 1 :=
begin
  rw [←one_nat, ←zero_nat],
  assume h,
  rw of_nat_cancel at h,
  from zero_ne_one h,
end

end quotint
end hidden
