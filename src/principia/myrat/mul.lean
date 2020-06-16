import .add

namespace hidden
open myint

namespace frac

def mul (x y : frac) : frac :=
⟨x.num * y.num, x.denom * y.denom,
by from zero_lt_mul x.denom_pos y.denom_pos⟩

instance: has_mul frac := ⟨mul⟩

theorem mul_num {x y : frac} :
(x * y).num = x.num * y.num := rfl

theorem mul_denom {x y : frac} :
(x * y).denom = x.denom * y.denom := rfl

theorem mul_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → ⟦a * x⟧ = ⟦b * y⟧ :=
begin
  assume hab hxy,
  rw setoid_equiv at hab hxy,
  apply quotient.sound,
  rw [setoid_equiv, mul_num, mul_num, mul_denom, mul_denom],
  -- State what we want ac_refl to do, then do it and rewrite
  have h₁ : a.num * x.num * (b.denom * y.denom) =
            x.num * y.denom * a.num * b.denom,
    ac_refl,
  rw [h₁, hxy],
  have h₂ : b.num * y.num * (a.denom * x.denom) =
            b.num * a.denom * x.denom * y.num,
    ac_refl,
  rw [h₂, ←hab],
  ac_refl,
end

-- Reciprocal of zero is zero
-- This has to be an if, because 0 is a different case
def inv (x : frac) : frac :=
if h : x.num = 0 then ⟨0, 1, zero_lt_one⟩ else
⟨(sign x.num) * x.denom, (sign x.num) * x.num, zero_lt_sign_mul_self h⟩

instance: has_inv frac := ⟨inv⟩

private theorem inv_ite {x : frac} : x⁻¹ = dite (x.num = 0) (λ (h : x.num = 0), ⟨0, 1, zero_lt_one⟩)
    (λ (h : ¬x.num = 0),⟨(sign x.num) * x.denom, (sign x.num) * x.num, zero_lt_sign_mul_self h⟩)
:= rfl

theorem inv_zero {x : frac} (h : x.num = 0) : x⁻¹ = ⟨0, 1, zero_lt_one⟩ :=
by rw [inv_ite, dif_pos h]

theorem inv_num_nonzero {x : frac} (h : x.num ≠ 0) :
x⁻¹.num = (sign x.num) * x.denom :=
by rw [inv_ite, dif_neg h]

theorem inv_denom_nonzero {x : frac} (h : x.num ≠ 0) :
x⁻¹.denom = (sign x.num) * x.num :=
by rw [inv_ite, dif_neg h]

theorem inv_well_defined (x y : frac) :
x ≈ y → ⟦x⁻¹⟧ = ⟦y⁻¹⟧ :=
begin
  assume hxy,
  rw setoid_equiv at hxy,
  apply quotient.sound,
  rw setoid_equiv,
  by_cases x.num = 0, {
    rw [h, myint.zero_mul] at hxy,
    have hzero := myint.mul_integral hxy.symm,
    cases hzero,
      exfalso, from (myint.lt_imp_ne x.denom_pos) hzero.symm,
    rw [inv_zero h, inv_zero hzero],
  }, {
    have hydn0 : y.denom ≠ 0,
      from (myint.lt_imp_ne y.denom_pos).symm,
    have hlhsn0 : x.num * y.denom ≠ 0,
      rw mul_nonzero_nonzero,
      split; assumption,
    have : y.num ≠ 0,
      rw hxy at hlhsn0,
      from (mul_nonzero_nonzero.mp hlhsn0).left,
    rw [inv_denom_nonzero h, inv_num_nonzero h],
    rw [inv_denom_nonzero this, inv_num_nonzero this],
    have h₁ : x.num.sign * x.denom * (y.num.sign * y.num) =
      x.num.sign * y.num.sign * (y.num * x.denom),
      ac_refl,
    rw [h₁, ←hxy],
    ac_refl,
  },
end

end frac

namespace myrat

def mul : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x * y⟧) frac.mul_well_defined

instance: has_mul myrat := ⟨mul⟩

def inv : myrat → myrat :=
quotient.lift (λ x, ⟦x⁻¹⟧) frac.inv_well_defined

instance: has_inv myrat := ⟨inv⟩

def div : myrat → myrat → myrat := λ x y, x * y⁻¹

instance: has_div myrat := ⟨div⟩

variables {x y z : myrat}

theorem div_eq_mul_inv : x / y = x * y⁻¹ := rfl

-- Multiplication

theorem mul_eq_cls {x y : frac} {a b : myrat} :
a = ⟦x⟧ → b = ⟦y⟧ → a * b = ⟦x * y⟧ :=
λ hax hby, by rw [hax, hby]; refl

theorem mul_comm (x y : myrat): x * y = y * x :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  rw [←ha, ←hb],
  repeat { rw mul_eq_cls rfl rfl, },
  rw class_equiv,
  repeat { rw frac.mul_num <|> rw frac.mul_denom, },
  ac_refl,
end

theorem mul_zero: x * 0 = 0 :=
begin
  cases quotient.exists_rep x with a ha,
  rw [←ha, rat_zero],
  rw mul_eq_cls rfl rfl,
  rw class_equiv,
  rw [frac.mul_num, frac.mul_denom],
  dsimp only [],
  repeat { rw myint.mul_zero <|> rw myint.zero_mul },
end

theorem zero_mul: 0 * x = 0 :=
by rw [mul_comm]; exact mul_zero

theorem mul_one: x * 1 = x :=
begin
  cases quotient.exists_rep x with a ha,
  rw [←ha, rat_one],
  rw mul_eq_cls rfl rfl,
  rw class_equiv,
  rw [frac.mul_num, frac.mul_denom],
  dsimp only [],
  rw [myint.mul_one, myint.mul_one],
end

theorem one_mul: 1 * x = x :=
by rw [mul_comm]; exact mul_one

instance mul_is_comm: is_commutative myrat mul := ⟨@mul_comm⟩

theorem mul_assoc: x * y * z = x * (y * z) :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  cases quotient.exists_rep z with c hc,
  rw [←ha, ←hb, ←hc],
  repeat { rw mul_eq_cls rfl rfl, },
  rw class_equiv,
  repeat { rw frac.mul_num <|> rw frac.mul_denom, },
  ac_refl,
end

instance mul_is_assoc: is_associative myrat mul := ⟨@mul_assoc⟩

theorem mul_add: x * (y + z) = x * y + x * z :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  cases quotient.exists_rep z with c hc,
  rw [←ha, ←hb, ←hc],
  repeat { rw mul_eq_cls rfl rfl <|> rw add_eq_cls rfl rfl, },
  rw class_equiv,
  repeat { rw frac.mul_num <|> rw frac.mul_denom <|> rw frac.add_num <|> rw frac.add_denom, },
  -- ac_refl can't expand brackets
  repeat { rw myint.add_mul <|> rw myint.mul_add, },
  ac_refl,
end

theorem add_mul: (x + y) * z = x * z + y * z :=
by rw [mul_comm, mul_add, mul_comm, mul_comm z]

theorem mul_with_neg : x * (-y) = -(x * y) := sorry

theorem mul_neg_with : (-x) * y = -(x * y) := sorry

-- Reciprocal "inv"

theorem inv_eq_cls {a : myrat} {x : frac}: a = ⟦x⟧ → a⁻¹ = ⟦x⁻¹⟧ :=
λ h, by rw h; refl

@[simp]
theorem one_inv : 1⁻¹ = (1 : myrat) :=
begin
  rw [rat_one, @inv_eq_cls _ ⟨1, 1, zero_lt_one⟩ rfl],
  rw class_equiv,
  rw [frac.inv_num_nonzero, frac.inv_denom_nonzero],
  all_goals { dsimp only [], },
  repeat { rw myint.one_mul <|> rw myint.mul_one, },
  all_goals { assume h, from myint.zero_ne_one h.symm, },
end

@[simp]
theorem zero_inv : 0⁻¹ = (0 : myrat) :=
begin
  rw [rat_zero, @inv_eq_cls _ ⟨0, 1, zero_lt_one⟩ rfl],
  rw [class_equiv, frac.inv_zero],
  refl,
end

@[simp]
theorem inv_inv : x⁻¹⁻¹ = x :=
begin
  cases quotient.exists_rep x with a ha,
  rw [←ha, inv_eq_cls rfl, inv_eq_cls rfl, class_equiv],
  by_cases a.num = 0, {
    have : a⁻¹.num = 0,
      rw frac.inv_zero h,
    rw [frac.inv_zero this, h, myint.zero_mul, myint.zero_mul],
  }, {
    have : a⁻¹.num ≠ 0,
      assume h0,
      rw frac.inv_num_nonzero h at h0,
      -- Similar pattern used in inv_well_defined
      have h₁: a.denom ≠ 0,
        from (myint.lt_imp_ne a.denom_pos).symm,
      have h₂: a.num.sign = 0,
        cases myint.mul_integral h0,
          contradiction,
        assumption,
      rw ←myint.zero_iff_sign_zero at h₂,
      contradiction,
    rw [frac.inv_num_nonzero this, frac.inv_denom_nonzero this],
    rw [frac.inv_num_nonzero h, frac.inv_denom_nonzero h],
    rw myint.sign_mult,
    ac_refl,
  },
end

theorem inv_distr : (x * y)⁻¹ = x⁻¹ * y⁻¹ :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  rw [←ha, ←hb],
  repeat { rw inv_eq_cls rfl <|> rw mul_eq_cls rfl rfl, },
  rw class_equiv,
  rw [frac.mul_num, frac.mul_denom],
  by_cases (a * b).num = 0,
    have : a.num = 0 ∨ b.num = 0,
      rw [frac.mul_num, myint.mul_comm] at h,
      from myint.mul_integral h,
    rw frac.inv_zero h,
    dsimp only [],
    rw [myint.zero_mul, myint.mul_one],
    cases this with ha hb,
      rw [frac.inv_zero ha, myint.zero_mul],
    rw [frac.inv_zero hb, myint.mul_zero],
  have : a.num ≠ 0 ∧ b.num ≠ 0,
    rwa [←myint.mul_nonzero_nonzero, ←frac.mul_num],
  rw [frac.inv_num_nonzero h, frac.inv_denom_nonzero h],
  rw [frac.inv_num_nonzero this.left, frac.inv_denom_nonzero this.left],
  rw [frac.inv_num_nonzero this.right, frac.inv_denom_nonzero this.right],
  rw [frac.mul_num, frac.mul_denom, sign_mult],
  ac_refl,
end

theorem inv_self_mul : x ≠ 0 → x⁻¹ * x = 1 :=
begin
  cases quotient.exists_rep x with a ha,
  assume hx,
  rw ha.symm at *,
  rw [inv_eq_cls rfl, mul_eq_cls rfl rfl, rat_one],
  rw class_equiv,
  dsimp only [],
  rw [frac.mul_num, frac.mul_denom],
  have : a.num ≠ 0,
    rw rat_zero at hx,
    have h : ¬⟦a⟧ = ⟦{num := 0, denom := 1, denom_pos := zero_lt_one}⟧,
      from hx,
    clear hx,
    rw [class_equiv, myint.mul_one, myint.zero_mul] at h,
    assumption,
  rw [frac.inv_num_nonzero this, frac.inv_denom_nonzero this],
  ac_refl,
end

theorem self_inv_mul : x ≠ 0 → x * x⁻¹ = 1 :=
begin
  assume h,
  rw mul_comm,
  exact inv_self_mul h,
end

-- Division

@[simp]
theorem div_one : x / 1 = x :=
by rw [div_eq_mul_inv, one_inv, mul_one]

theorem one_div : 1 / x = x⁻¹ :=
by rw [div_eq_mul_inv, one_mul]

@[simp]
theorem zero_div : 0 / x = 0 :=
by rw [div_eq_mul_inv, zero_mul]

@[simp]
theorem div_zero : x / 0 = 0 :=
by rw [div_eq_mul_inv, zero_inv, mul_zero]

theorem mul_div_cancel : y ≠ 0 → (x * y) / y = x :=
λ h, by rw [div_eq_mul_inv, mul_assoc, self_inv_mul h, mul_one]

theorem div_mul_cancel : y ≠ 0 → (x / y) * y = x :=
λ h, by rw [div_eq_mul_inv, mul_assoc, inv_self_mul h, mul_one]

theorem self_div : x ≠ 0 → x / x = 1 :=
λ h, by rw [div_eq_mul_inv, self_inv_mul h]

theorem div_inv_switch : x / y = (y / x)⁻¹ :=
by rw [div_eq_mul_inv, div_eq_mul_inv, inv_distr, inv_inv, mul_comm]

theorem add_div : (x + y) / z = x / z + y / z :=
by repeat { rw div_eq_mul_inv, }; rw add_mul

theorem one_plus_one : 1 + 1 = (2 : myrat):= rfl

theorem double_eq_add_self : 2 * x = x + x :=
by rw [←one_plus_one, add_mul, one_mul]

theorem half_plus_half {ε : myrat} : ε / 2 + ε / 2 = ε :=
begin
  rw [←double_eq_add_self, mul_comm, div_mul_cancel two_nzero],
end

-- I'm sure I proved this somewhere else
theorem abs_mul : abs (x * y) = abs x * abs y :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  cases quotient.exists_rep y with b hb, subst hb,
  rw mul_eq_cls rfl rfl,
  repeat {rw abs_eq_cls rfl},
  rw mul_eq_cls rfl rfl,
  rw class_equiv,
  repeat {rw frac.abs_num <|> rw frac.abs_denom},
  repeat {rw frac.mul_num <|> rw frac.mul_denom},  
  repeat {rw frac.abs_num <|> rw frac.abs_denom},
  rw ←myint.abs_distr,
  rw myint.nat_nat_mul,
end

end myrat

end hidden
