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

theorem inv_cancel : x⁻¹ = y⁻¹ ↔ x = y :=
begin
  split; assume h, {
    rw ←inv_inv y,
    apply inv_unique,
    rw ←h,
    conv {
      to_lhs, congr, congr, skip,
      rw ←inv_inv x,
    },
    apply exists_inv,
  }, {
    rw h,
  },
end

theorem right_mul : x = y → x * z = y * z :=
begin
  assume h,
  congr,
  assumption,
end

theorem left_mul : x = y → z * x = z * y :=
begin
  assume h,
  congr,
  assumption,
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

-- We consider the following relation on α
def R := x * x⁻¹ = y * y⁻¹
infix ` ≅ `:50 := R

theorem cong_def : x ≅ y ↔ x * x⁻¹ = y * y⁻¹ := by refl

-- It's an equivalence relation
@[refl]
theorem cong_refl : x ≅ x := by from rfl

@[symm]
theorem cong_symm : x ≅ y → y ≅ x :=
begin
  assume h,
  rw cong_def,
  symmetry,
  assumption,
end

@[trans]
theorem cong_trans : x ≅ y → y ≅ z → x ≅ z :=
begin
  assume hxy hyz,
  rw cong_def at ⊢ hxy,
  rw hxy,
  assumption,
end

lemma cong_iff_right_multiple : x ≅ y ↔ ∃ z, x = y * z :=
begin
  split; assume h, {
    rw cong_def at h,
    existsi y⁻¹ * x,
    rw [←mul_assoc, ←h],
    symmetry,
    apply exists_inv,
  }, {
    cases h with z h,
    rw [cong_def, ←id_inv],
    symmetry,
    apply inv_unique,
    conv {
      to_lhs,
      rw mul_assoc,
      congr, skip,
      rw ←mul_assoc,
      congr,
      rw [h, ←mul_assoc, exists_inv, ←h],
    },
    rw [←mul_assoc, exists_inv],
  },
end

lemma invs_cong_iff_left_multiple : x⁻¹ ≅ y⁻¹ ↔ ∃ z, x = z * y :=
begin
  split; assume h, {
    rw [cong_def, inv_inv x, inv_inv y] at h,
    existsi x * y⁻¹,
    rw [mul_assoc, ←h, ←mul_assoc, exists_inv],
  }, {
    cases h with z h,
    rw cong_def,
    rw ←id_inv,
    symmetry,
    apply inv_unique,
    rw inv_inv x,
    rw inv_inv y,
    conv {
      to_lhs,
      congr,
      rw mul_assoc,
      congr, skip,
      rw h,
      rw mul_assoc,
      congr, skip,
      rw ←mul_assoc,
      rw exists_inv,
    },
    rw ←h,
    rw mul_assoc,
    rw ←mul_assoc x,
    rw exists_inv,
  },
end

lemma useful : x⁻¹ * x = (x * x)⁻¹ * x * x :=
begin
  suffices : x⁻¹ ≅ (x * x)⁻¹,
    rwa [cong_def, inv_inv x, inv_inv (x * x), ←mul_assoc] at this,
  symmetry,
  rw invs_cong_iff_left_multiple,
  existsi x,
  refl,
end

theorem cong_inv : x ≅ x⁻¹ :=
begin
  rw cong_iff_right_multiple,
  existsi x * x,
  symmetry,
  rw ←inv_cancel,
  apply inv_unique,
  conv { to_rhs, rw ←exists_inv x, rw mul_assoc },
  rw mul_assoc,
  apply left_mul,
  rw useful,
  apply right_mul,
  symmetry,
  apply inv_unique,
  conv {
    to_lhs,
    rw mul_assoc,
    congr, skip,
    rw mul_assoc,
    congr, skip,
    rw [←mul_assoc, ←mul_assoc, exists_inv],
  },
  rw mul_assoc,
  conv {
    to_lhs,
    congr, skip,
    rw [←mul_assoc, exists_inv],
  },
end

theorem id_swap : x * x⁻¹ = x⁻¹ * x :=
begin
  conv {
    to_rhs,
    congr, skip,
    rw ←inv_inv x,
  },
  apply cong_inv,
end

-- Could this be earlier?
lemma cong_inv_iff_left_multiple : x ≅ y⁻¹ ↔ ∃ z, x = z * y :=
begin
  split; assume h, {
    rw cong_def at h,
    rw inv_inv at h,
    existsi x * y⁻¹,
    rw [mul_assoc, ←h, id_swap, ←mul_assoc, exists_inv],
  }, {
    cases h with z h,
    rw [cong_def, inv_inv, ←id_swap, ←id_inv],
    symmetry,
    apply inv_unique,
    rw [id_swap, id_swap y],
    conv {
      to_lhs,
      congr,
      rw mul_assoc,
      congr, skip,
      rw [h, mul_assoc],
      congr, skip,
      rw [←mul_assoc, exists_inv],
    },
    rw [←h, mul_assoc, ←mul_assoc x, exists_inv],
  },
end

theorem cong_comm : x * y ≅ y * x :=
begin
  transitivity x, {
    rw cong_iff_right_multiple,
    existsi y,
    refl,
  },
  transitivity x⁻¹, apply cong_inv,
  symmetry,
  rw cong_inv_iff_left_multiple,
  existsi y,
  refl,
end

-- It turns out everything is related
theorem cong_trivial : x ≅ y :=
begin
  transitivity x * y, {
    symmetry,
    rw cong_iff_right_multiple,
    existsi y,
    refl,
  }, {
    transitivity y * x,
      apply cong_comm,
    rw cong_iff_right_multiple,
    existsi x,
    refl,
  },
end

-- So set the identitiy to be this unique value
theorem id_unique : x * x⁻¹ = y * y⁻¹ := cong_trivial x y

-- Instantiate it as a mygroup class
instance: hidden.mygroup α := {
  e := (default α) * (default α)⁻¹,
  mul_assoc := mul_assoc,
  mul_id := λ a, by rw [id_unique (default α) a⁻¹, inv_inv, ←mul_assoc, exists_inv],
  mul_inv := λ a, id_unique _ _
}

end gareth
