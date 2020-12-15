import ..myring.order
import ..myring.integral_domain

namespace hidden

class myfield (α : Type) extends myring α, has_inv α :=
(mul_inv (x : α): x ≠ 0 → x * x⁻¹ = 1)
(nontrivial: (0: α) ≠ 1)

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


-- @[simp]
-- theorem one_inv : 1⁻¹ = (1 : myrat) :=
-- begin
--   rw [rat_one, @inv_eq_cls _ ⟨1, 1, one_pos⟩ rfl],
--   rw class_equiv,
--   rw [frac.inv_num_nonzero, frac.inv_denom_nonzero],
--   all_goals { dsimp only [], },
--   repeat { rw one_mul <|> rw mul_one, },
--   all_goals { assume h, from myint.nontrivial h.symm, },
-- end

-- @[simp]
-- theorem inv_inv : x⁻¹⁻¹ = x :=
-- begin
--   cases quotient.exists_rep x with a ha,
--   rw [←ha, inv_eq_cls rfl, inv_eq_cls rfl, class_equiv],
--   by_cases a.num = 0, {
--     have : a⁻¹.num = 0,
--       rw frac.inv_zero h,
--     rw [frac.inv_zero this, h, zero_mul, zero_mul],
--   }, {
--     have : a⁻¹.num ≠ 0,
--       assume h0,
--       rw frac.inv_num_nonzero h at h0,
--       -- Similar pattern used in inv_well_defined
--       have h₁: a.denom ≠ 0,
--         from (lt_impl_ne _ _ a.denom_pos).symm,
--       have h₂: sign a.num = 0,
--         cases integral_domain.mul_integral _ _ h0,
--           assumption,
--         contradiction,
--       rw sign_zero_iff_zero at h₂,
--       contradiction,
--     rw [frac.inv_num_nonzero this, frac.inv_denom_nonzero this],
--     rw [frac.inv_num_nonzero h, frac.inv_denom_nonzero h],
--     rw sign_mul,
--     ac_refl,
--     apply integral_domain.mul_integral,
--   },
-- end

-- theorem inv_distr : (x * y)⁻¹ = x⁻¹ * y⁻¹ :=
-- begin
--   cases quotient.exists_rep x with a ha,
--   cases quotient.exists_rep y with b hb,
--   rw [←ha, ←hb],
--   repeat { rw inv_eq_cls rfl <|> rw mul_eq_cls rfl rfl, },
--   rw class_equiv,
--   rw [frac.mul_num, frac.mul_denom],
--   by_cases (a * b).num = 0,
--     have : a.num = 0 ∨ b.num = 0,
--       rw [frac.mul_num, myint.mul_comm] at h,
--       from myint.mul_integral h,
--     rw frac.inv_zero h,
--     dsimp only [],
--     rw [myint.zero_mul, myint.mul_one],
--     cases this with ha hb,
--       rw [frac.inv_zero ha, myint.zero_mul],
--     rw [frac.inv_zero hb, myint.mul_zero],
--   have : a.num ≠ 0 ∧ b.num ≠ 0,
--     rwa [←myint.mul_nonzero_nonzero, ←frac.mul_num],
--   rw [frac.inv_num_nonzero h, frac.inv_denom_nonzero h],
--   rw [frac.inv_num_nonzero this.left, frac.inv_denom_nonzero this.left],
--   rw [frac.inv_num_nonzero this.right, frac.inv_denom_nonzero this.right],
--   rw [frac.mul_num, frac.mul_denom, sign_mul],
--   ac_refl,
-- end


-- theorem self_inv_mul : x ≠ 0 → x * x⁻¹ = 1 :=
-- begin
--   assume h,
--   rw mul_comm,
--   exact inv_self_mul h,
-- end


-- -- Division

-- @[simp]
-- theorem div_one : x / 1 = x :=
-- by rw [div_eq_mul_inv, one_inv, mul_one]

-- theorem one_div : 1 / x = x⁻¹ :=
-- by rw [div_eq_mul_inv, one_mul]

-- @[simp]
-- theorem zero_div : 0 / x = 0 :=
-- by rw [div_eq_mul_inv, zero_mul]

-- @[simp]
-- theorem div_zero : x / 0 = 0 :=
-- by rw [div_eq_mul_inv, zero_inv, mul_zero]

-- theorem mul_div_cancel : y ≠ 0 → (x * y) / y = x :=
-- λ h, by rw [div_eq_mul_inv, mul_assoc, self_inv_mul h, mul_one]

-- theorem div_mul_cancel : y ≠ 0 → (x / y) * y = x :=
-- λ h, by rw [div_eq_mul_inv, mul_assoc, inv_self_mul h, mul_one]

-- theorem self_div : x ≠ 0 → x / x = 1 :=
-- λ h, by rw [div_eq_mul_inv, self_inv_mul h]

-- theorem div_inv_switch : x / y = (y / x)⁻¹ :=
-- by rw [div_eq_mul_inv, div_eq_mul_inv, inv_distr, inv_inv, mul_comm]

-- theorem add_div : (x + y) / z = x / z + y / z :=
-- by repeat { rw div_eq_mul_inv, }; rw add_mul

-- theorem one_plus_one : 1 + 1 = (2 : myrat):= rfl

-- theorem double_eq_add_self : 2 * x = x + x :=
-- by rw [←one_plus_one, add_mul, one_mul]

-- theorem half_plus_half {ε : myrat} : ε / 2 + ε / 2 = ε :=
-- begin
--   rw [←double_eq_add_self, mul_comm, div_mul_cancel two_nzero],
-- end


instance: integral_domain α := ⟨begin
  intros a b ha hba,
  rw [←myring.mul_one b, ←mul_inv a ha, ←myring.mul_assoc, hba, myring.zero_mul],
end⟩

def div : α → α → α := λ a b, a * b⁻¹
instance: has_div α := ⟨div⟩

end myfield

end hidden
