-- Gareth's question

import ..logic
import .basic

class gareth (α : Type)
extends has_mul α, has_inv α, inhabited α :=
(mul_assoc (x y z : α): x * y * z = x * (y * z))
(exists_inv (x : α): x * (x⁻¹) * x = x)
(inv_unique (x y : α): x * y * x = x → y = x⁻¹)

namespace gareth

variables {α : Type} [gareth α] (x y z : α)

theorem inv_inv : x⁻¹⁻¹ = x :=
begin
  symmetry,
  apply inv_unique,
  apply inv_unique,
  conv {
    to_lhs,
    congr,
      rw ←mul_assoc,
      congr,
        rw [←mul_assoc, exists_inv],
  },
  rw exists_inv,
end

theorem id_inv : (x * x⁻¹)⁻¹ = x * x⁻¹ :=
begin
  symmetry,
  apply inv_unique,
  conv {
    congr, congr,
    rw [←mul_assoc, exists_inv],
  },
  rw [←mul_assoc, exists_inv],
end

theorem id_swap : x * x⁻¹ = x⁻¹ * x := sorry

theorem id_unique : x * x⁻¹ = y * y⁻¹ :=
begin
  transitivity (x * y) * (x * y)⁻¹, {
    rw ←id_inv (x * y),
    apply inv_unique,
    conv {
      congr,
      rw mul_assoc,
      congr, skip,
      rw [←mul_assoc, ←mul_assoc, exists_inv],
    },
    suffices : (x * y) * (x * y)⁻¹ * (x * y) = x * y,
      rw [←mul_assoc, this],
    apply exists_inv,
  }, {
    rw [←id_inv (x * y), id_swap (x * y)],
    symmetry,
    apply inv_unique,
    conv {
      congr,
      congr,
      rw [mul_assoc, mul_assoc x, id_swap y, ←mul_assoc y, exists_inv y],
    },
    rw [←id_swap (x * y), ←mul_assoc, exists_inv],
  },
end

-- Instantiate it as a mygroup class
instance: hidden.mygroup α := {
  e := (default α) * (default α)⁻¹,
  mul_assoc := mul_assoc,
  mul_id := λ a, by rw [id_unique (default α) a⁻¹, inv_inv, ←mul_assoc, exists_inv],
  mul_inv := λ a, id_unique _ _
}

end gareth
