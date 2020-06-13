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
def inv (x : frac) : frac :=
if h : x.num = 0 then ⟨0, 1, zero_lt_one⟩ else
⟨(sign x.num) * x.denom, (sign x.num) * x.num, zero_lt_sign_mul_self h⟩

instance: has_inv frac := ⟨inv⟩

-- TODO: inv_num & inv_denom

theorem inv_well_defined (x y : frac) :
x ≈ y → ⟦x⁻¹⟧ = ⟦y⁻¹⟧ := sorry

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

theorem mul_zero: x * 0 = 0 := sorry

theorem zero_mul: 0 * x = 0 := sorry

theorem mul_one: x * 1 = x := sorry

theorem one_mul: 1 * x = x := sorry

theorem mul_comm: x * y = y * x := sorry

instance mul_is_comm: is_commutative myrat mul := ⟨@mul_comm⟩

theorem mul_assoc: x * y * z = x * (y * z) := sorry

instance mul_is_assoc: is_associative myrat mul := ⟨@mul_assoc⟩

theorem mul_add: x * (y + z) = x * y + x * z := sorry

theorem add_mul: (x + y) * z = x * z + y * z := sorry

-- Reciprocal "inv"

@[simp]
theorem one_inv : 1⁻¹ = (1 : myrat) := sorry

@[simp]
theorem zero_inv : 0⁻¹ = (0 : myrat) := sorry

@[simp]
theorem inv_inv : x⁻¹⁻¹ = x := sorry

theorem inv_distr : (x * y)⁻¹ = x⁻¹ * y⁻¹ := sorry

theorem inv_self_mul : x ≠ 0 → x⁻¹ * x = 1 := sorry

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

-- I don't know how to prove this
private theorem idkhow1 : (2 : myrat) = 1 + 1 := sorry

theorem double_eq_add_self : 2 * x = x + x :=
by rw [idkhow1, add_mul, one_mul]

-- I don't know how to prove this
private theorem idkhow2 : (2 : myrat) ≠ 0 := sorry

theorem half_plus_half {ε : myrat} : ε / 2 + ε / 2 = ε :=
begin
  rw [←double_eq_add_self, mul_comm, div_mul_cancel idkhow2],
end

end myrat

end hidden
