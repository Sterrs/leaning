import ..myring.order
import ..myring.integral_domain

namespace hidden

class myfield (α : Type) extends myring α, has_inv α :=
(mul_inv (x : α): x ≠ 0 → x * x⁻¹ = 1)

namespace myfield

variables {α : Type} [myfield α] (x y z : α)

theorem inv_mul (hx : x ≠ 0) : x⁻¹ * x = 1 :=
begin
  rw [myring.mul_comm],
  apply mul_inv _ hx,
end

theorem nzero_impl_inv_nzero (hx : x ≠ 0) : x⁻¹ ≠ 0 :=
begin
  assume hinv0,
  apply hx,
  apply myring.one_eq_zero_impl_all_zero,
  rw [←mul_inv _ hx, hinv0, myring.mul_zero],
end

instance: integral_domain α := ⟨begin
  intros a b ha hba,
  rw [←myring.mul_one b, ←mul_inv a ha, ←myring.mul_assoc, hba, myring.zero_mul],
end⟩

def div : α → α → α := λ a b, a * b⁻¹
instance: has_div α := ⟨div⟩

end myfield

end hidden
