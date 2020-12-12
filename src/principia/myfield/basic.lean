import ..myring.order

namespace hidden

class myfield (α : Type) extends myring α, has_inv α :=
(mul_inv (t : α): t ≠ 0 → t * t⁻¹ = 1)

namespace myfield

variables {α : Type} [myfield α] (x y z : α)
variables (s t : α) -- Try to use s, t when non-zero

theorem inv_mul (ht : t ≠ 0) : t⁻¹ * t = 1 :=
begin
  rw [myring.mul_comm],
  apply mul_inv,
  from ht,
end

def div : α → α → α := λ a b, a * b⁻¹
instance: has_div α := ⟨div⟩

end myfield

end hidden
