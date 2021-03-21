import .frac
import ..myfield.basic

namespace hidden

open myint
open myring
open ordered_myring

def myrat := quotient frac.frac.setoid

namespace myrat

instance: decidable_eq myrat := quotient.decidable_eq

private lemma class_setoid (x y : frac) :
⟦x⟧ = ⟦y⟧ ↔ x ≈ y := iff.intro quotient.exact quotient.sound

theorem class_equiv {x y : frac} :
⟦x⟧ = ⟦y⟧ ↔ x.num * y.denom = y.num * x.denom :=
begin
  split; assume h,
    rwa [←frac.setoid_equiv, ←class_setoid],
  rwa [class_setoid, frac.setoid_equiv],
end

def neg : myrat → myrat :=
quotient.lift (λ x, ⟦-x⟧) frac.neg_well_defined

instance: has_neg myrat := ⟨neg⟩
instance has_neg2: has_neg (quotient frac.frac.setoid) := ⟨neg⟩

private theorem neg_eq_cls {x: frac}:
-⟦x⟧ = ⟦-x⟧ := rfl

private lemma one_pos: (0: myint) < 1 := nontrivial_zero_lt_one myint.nontrivial

instance: has_zero myrat := ⟨⟦⟨0, 1, one_pos⟩⟧⟩

theorem rat_zero: (0: myrat) = ⟦⟨0, 1, one_pos⟩⟧ := rfl

instance: has_one myrat := ⟨⟦⟨1, 1, one_pos⟩⟧⟩

theorem rat_one: (1: myrat) = ⟦⟨1, 1, one_pos⟩⟧ := rfl

instance: has_coe myint myrat := ⟨λ m, ⟦⟨m, 1, one_pos⟩⟧⟩

private theorem nontrivial: (0: myrat) ≠ 1 :=
begin
  assume hydroxide,
  have := quotient.exact hydroxide,
  rw frac.setoid_equiv at this,
  cases quotient.exact this,
end

theorem coe_int {m : myint} : (↑m : myrat) = ⟦⟨m, 1, one_pos⟩⟧ :=
rfl

theorem coe_cancel {m n : myint}:
(↑m : myrat) = ↑n ↔ m = n :=
begin
  split; assume h, {
    rw [coe_int, coe_int, class_equiv] at h,
    dsimp only [] at h,
    rwa [mul_one, mul_one] at h,
  }, {
    congr, assumption,
  },
end

def add : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x + y⟧) frac.add_well_defined

instance: has_add myrat := ⟨add⟩
instance has_add2: has_add (quotient frac.frac.setoid) := ⟨add⟩

private theorem add_eq_cls {x y: frac}:
⟦x⟧ + ⟦y⟧ = ⟦x + y⟧ := rfl

-- Posterity
private theorem two_nzero: (2: myrat) ≠ 0 :=
begin
  assume water,
  have := quotient.exact water,
  rw frac.setoid_equiv at this,
  cases (quotient.exact this),
end

def sub (x y : myrat) : myrat :=
x + -y

instance: has_sub myrat := ⟨sub⟩
instance has_sub2: has_sub (quotient frac.frac.setoid) := ⟨sub⟩

private theorem sub_eq_cls {x y: frac}:
⟦x⟧ - ⟦y⟧ = ⟦x + -y⟧ := rfl

variables {x y z : myrat}
variables {m n k : myint}

theorem add_coe: (↑m : myrat) + ↑n = ↑(m + n) :=
begin
  repeat { rw coe_int, },
  apply congr_arg quotient.mk,
  rw ←frac.frac_add_add,
  dsimp [frac.add],
  repeat {rw mul_one},
  refl,
end

theorem neg_coe: -(↑m : myrat) = ↑(-m) :=
begin
  repeat { rw coe_int, },
  rw [neg_eq_cls, frac.frac_neg_neg],
  dsimp [frac.neg],
  refl,
end

def mul : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x * y⟧) frac.mul_well_defined

instance: has_mul myrat := ⟨mul⟩
instance has_mul2: has_mul (quotient frac.frac.setoid) := ⟨mul⟩

def inv : myrat → myrat :=
quotient.lift (λ x, ⟦x⁻¹⟧) frac.inv_well_defined

instance: has_inv myrat := ⟨inv⟩
instance has_inv2: has_inv (quotient frac.frac.setoid) := ⟨inv⟩

-- Multiplication

private theorem mul_eq_cls {x y : frac}:
⟦x⟧ * ⟦y⟧ = ⟦x * y⟧ := rfl

-- Reciprocal "inv"

private theorem inv_eq_cls {x : frac}:
⟦x⟧⁻¹ = ⟦x⁻¹⟧ := rfl

@[simp]
theorem zero_inv : 0⁻¹ = (0 : myrat) :=
rfl

private theorem inv_self_mul : x ≠ 0 → x * x⁻¹ = 1 :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  assume hx,
  rw [inv_eq_cls, mul_eq_cls, rat_one],
  rw class_equiv,
  dsimp only [],
  rw [frac.mul_num, frac.mul_denom],
  have : a.num ≠ 0,
    rw rat_zero at hx,
    have h : ¬⟦a⟧ = ⟦{num := 0, denom := 1, denom_pos := one_pos}⟧,
      from hx,
    clear hx,
    rw [class_equiv, mul_one, zero_mul] at h,
    assumption,
  rw [frac.inv_num_nonzero this, frac.inv_denom_nonzero this],
  ac_refl,
end

instance: myring myrat := ⟨
  λ x y z: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    cases quotient.exists_rep z with c hc, subst hc,
    apply congr_arg quotient.mk,
    rw frac.num_and_denom_eq,
    repeat { rw frac.add_num <|> rw frac.add_denom <|> rw myring.add_mul },
    split; ac_refl,
  end,
  λ x: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    rw [rat_zero, add_eq_cls],
    rw frac.sound_exact_iff,
    rw frac.setoid_equiv,
    rw frac.add_denom,
    rw frac.add_num,
    dsimp only [],
    rw myring.zero_mul,
    rw myring.add_zero,
    repeat {rw myring.mul_one},
  end,
  λ x: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    rw neg_eq_cls,
    rw add_eq_cls,
    apply quotient.sound,
    rw frac.setoid_equiv,
    dsimp only [],
    repeat {rw myring.zero_mul},
    rw frac.add_num,
    rw mul_one,
    rw frac.neg_denom,
    rw frac.neg_num,
    rw neg_mul,
    from add_neg _,
  end,
  λ x y z: myrat,
  begin
    cases quotient.exists_rep x with a ha,
    cases quotient.exists_rep y with b hb,
    cases quotient.exists_rep z with c hc,
    rw [←ha, ←hb, ←hc],
    repeat {rw mul_eq_cls,},
    rw class_equiv,
    repeat { rw frac.mul_num <|> rw frac.mul_denom, },
    ac_refl,
  end,
  λ x y: myrat,
  begin
    cases quotient.exists_rep x with a ha,
    cases quotient.exists_rep y with b hb,
    rw [←ha, ←hb],
    repeat {rw mul_eq_cls,},
    rw class_equiv,
    repeat { rw frac.mul_num <|> rw frac.mul_denom, },
    ac_refl,
  end,
  λ x: myrat,
  begin
    cases quotient.exists_rep x with a ha,
    rw [←ha, rat_one],
    rw mul_eq_cls,
    rw class_equiv,
    rw [frac.mul_num, frac.mul_denom],
    dsimp only [],
    repeat {rw myring.mul_one},
  end,
  λ x y z: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    cases quotient.exists_rep z with c hc, subst hc,
    repeat { rw mul_eq_cls <|> rw add_eq_cls, },
    rw class_equiv,
    repeat { rw frac.mul_num <|> rw frac.mul_denom <|> rw frac.add_num <|> rw frac.add_denom, },
    -- ac_refl can't expand brackets
    repeat { rw myring.add_mul <|> rw myring.mul_add, },
    ac_refl,
  end⟩

instance: myfield myrat := {
  mul_inv := λ x hx, inv_self_mul hx,
  nontrivial := nontrivial
}

-- Moved here as they might be useful
-- theorem one_plus_one : 1 + 1 = (2 : myrat):= rfl

-- theorem double_eq_add_self : 2 * x = x + x :=
-- by rw [←one_plus_one, add_mul, one_mul]

-- theorem half_plus_half {ε : myrat} : ε / 2 + ε / 2 = ε :=
-- begin
--   rw [←double_eq_add_self, mul_comm, div_mul_cancel two_nzero],
-- end

end myrat

end hidden
