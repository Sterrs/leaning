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

-- Dividing by zero gives you zero
def div (x y : frac) : frac :=
x * y⁻¹

instance: has_div frac := ⟨div⟩

theorem div_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → ⟦a / x⟧ = ⟦b / y⟧ := sorry

end frac

namespace myrat

def mul : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x * y⟧) frac.mul_well_defined

instance: has_mul myrat := ⟨mul⟩

def inv : myrat → myrat :=
quotient.lift (λ x, ⟦x⁻¹⟧) frac.inv_well_defined

instance: has_inv myrat := ⟨inv⟩

def div : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x / y⟧) frac.div_well_defined

instance: has_div myrat := ⟨div⟩

variables {x y z : myrat}

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

theorem one_inv : 1⁻¹ = (1 : myrat) := sorry

theorem zero_inv : 0⁻¹ = (0 : myrat) := sorry

theorem inv_self_mul : x⁻¹ * x = 1 := sorry

theorem self_inv_mul : x * x⁻¹ = 1 :=
by rw [mul_comm, inv_self_mul]

-- Division

theorem div_one : x / 1 = x := sorry

theorem one_div : 1 / x = x⁻¹ := sorry

theorem zero_div : 0 / x = 0 := sorry

theorem div_zero : x / 0 = 0 := sorry

-- This is sadly false when x = 0
theorem self_div : x / x = 1 := sorry

theorem div_switch : x / y = (y / x)⁻¹ := sorry

end myrat

end hidden
