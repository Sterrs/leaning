import ..myring.order
import ..myring.integral_domain

namespace hidden

class myfield (α : Type) extends myring α, has_inv α :=
(mul_inv {x : α}: x ≠ 0 → x * x⁻¹ = 1)
(nontrivial: (0: α) ≠ 1)

namespace myfield

open myring

variables {α : Type} [myfield α] (x y z : α)

theorem one_ne_zero : (1 : α) ≠ 0 :=
begin
  assume h,
  apply @nontrivial α,
  symmetry,
  assumption,
end

theorem zero_ne_one : (0 : α) ≠ 1 := nontrivial

theorem inv_mul {x : α} (hx : x ≠ 0) : x⁻¹ * x = 1 :=
begin
  rw [mul_comm],
  apply mul_inv hx,
end

theorem nzero_impl_inv_nzero (hx : x ≠ 0) : x⁻¹ ≠ 0 :=
begin
  assume hinv0,
  apply hx,
  apply one_eq_zero_impl_all_zero,
  rw [←mul_inv hx, hinv0, myring.mul_zero],
end

instance: integral_domain α := ⟨begin
  intros a b ha hba,
  rw [←myring.mul_one b, ←mul_inv ha, ←myring.mul_assoc, hba, myring.zero_mul],
end⟩

open integral_domain

theorem inv_unique {x : α} (y : α) (hx : x ≠ 0) : x * y = 1 → y = x⁻¹ :=
begin
  intro hxy,
  apply mul_cancel_left x,
    exact hx,
  rw hxy,
  symmetry,
  exact mul_inv hx,
end

@[simp] theorem one_inv : 1⁻¹ = (1 : α) := begin
  symmetry,
  apply inv_unique,
    exact one_ne_zero,
  rw one_mul,
end

theorem inv_nzero {x : α} (hx : x ≠ 0) : x⁻¹ ≠ 0 :=
begin
  intro hx0,
  apply @nontrivial α,
  rw [←mul_inv hx, ←mul_zero x, hx0],
end

theorem inv_inv {x : α} (hx : x ≠ 0) : x⁻¹⁻¹ = x :=
begin
  apply mul_cancel_right _ x⁻¹,
    exact inv_nzero hx,
  rw mul_comm,
  transitivity (1 : α),
    apply mul_inv,
    exact inv_nzero hx,
  symmetry,
  apply mul_inv hx,
end

theorem inv_inj {x y : α} (hx : x ≠ 0) (hy : y ≠ 0): x⁻¹ = y⁻¹ → x = y :=
begin
  intro hxy,
  rw [←inv_inv hx, ←inv_inv hy],
  congr,
  assumption,
end

theorem inv_distr {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) : (x * y)⁻¹ = x⁻¹ * y⁻¹ :=
begin
  have hxy : x * y ≠ 0 := mul_nzero hx hy,
  apply mul_cancel_right _ (x * y),
    exact hxy,
  rw [mul_comm, mul_inv hxy, mul_comm x, mul_assoc, ←mul_assoc y⁻¹, mul_comm y⁻¹,
      mul_inv hy, one_mul, inv_mul hx],
end

def div : α → α → α := λ a b, a * b⁻¹
instance: has_div α := ⟨div⟩

-- -- Division

theorem div_def : x / y = x * y⁻¹ := rfl

@[simp] theorem div_one : x / 1 = x :=
begin
  change x * 1⁻¹ = x,
  rw [one_inv, mul_one],
end

theorem one_div : 1 / x = x⁻¹ :=
begin
  change 1 * x⁻¹ = x⁻¹,
  rw one_mul,
end

@[simp] theorem zero_div : 0 / x = 0 :=
begin
  change 0 * x⁻¹ = 0,
  rw zero_mul,
end

theorem mul_div_cancel : y ≠ 0 → (x * y) / y = x :=
begin
  intro hy,
  change x * y * y⁻¹ = x,
  rw [mul_assoc, mul_inv hy, mul_one],
end

theorem div_mul_cancel : y ≠ 0 → (x / y) * y = x :=
begin
  intro hy,
  change x * y⁻¹ * y = x,
  rw [mul_assoc, inv_mul hy, mul_one],
end

theorem div_self {x : α} : x ≠ 0 → x / x = 1 :=
begin
  intro hx,
  change x * x⁻¹ = 1,
  exact mul_inv hx,
end

theorem div_inv_switch {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) : x / y = (y / x)⁻¹ :=
begin
  change x * y⁻¹ = (y * x⁻¹)⁻¹,
  rw [inv_distr hy (inv_nzero hx), inv_inv hx, mul_comm],
end

theorem add_div : (x + y) / z = x / z + y / z :=
begin
  change (x + y) * z⁻¹ = x * z⁻¹ + y * z⁻¹,
  apply add_mul,
end

-- Handy
theorem half_plus_half (water : 2 ≠ (0 : α)) (ε : α) : ε / 2 + ε / 2 = ε :=
begin
  rw [div_def, ←mul_add, ←one_div, ←add_div],
  change ε * (2 / 2) = ε,
  rw [div_self water, mul_one],
end

theorem minus_half (water : 2 ≠ (0 : α)) (ε : α) : ε - ε /2 = ε / 2 := sorry

end myfield

end hidden
