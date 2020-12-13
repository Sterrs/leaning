import .basic

namespace hidden

-- Can't extend field and ordered_myring as they both extend myring >:(
class ordered_myfield (α : Type) [has_le α] [ordered_myring α] extends myfield α

namespace ordered_myfield

variables {α : Type} [has_le α] [ordered_myring α] [ordered_myfield α] (x y z : α)
variables (s t : α) -- Try to use s, t when non-zero

-- theorem half_pos {ε : α} : 0 < ε → 0 < ε / 2 :=
-- assume h, by rwa [lt_mul_pos_right zero_lt_two, zero_mul, div_mul_cancel two_nzero]

-- theorem exists_between (a c : α) :
-- a < c → ∃ b : α, a < b ∧ b < c :=
-- begin
--   assume hac,
--   existsi (a + c) / 2,
--   split; rw add_div, {
--     rw [lt_add_left (-(a/2)), ←add_assoc, add_comm _ a, neg_self_add],
--     conv {
--       to_lhs,
--       congr,
--         rw ←@half_plus_half a, skip,
--       skip,
--     },
--     rw [add_assoc, self_neg_add, add_zero, zero_add],
--     rwa [lt_mul_pos_right zero_lt_two, div_mul_cancel two_nzero,
--          div_mul_cancel two_nzero],
--   }, {
--     rw [lt_add_right (-(c / 2)), add_assoc, self_neg_add],
--     conv {
--       to_rhs,
--       congr,
--         rw ←@half_plus_half c, skip,
--       skip,
--     },
--     rw [add_assoc, self_neg_add, add_zero, add_zero],
--     rwa [lt_mul_pos_right zero_lt_two, div_mul_cancel two_nzero,
--          div_mul_cancel two_nzero],
--   },
-- end

-- theorem lt_mul_comb_nonneg (a b x y : α): 0 ≤ a → 0 ≤ x → a < b → x < y → a * x < b * y :=
-- begin
--   assume h0a h0x hab hxy haxby,
--   have := le_mul_comb_nonneg _ _ _ _ h0a h0x
--     (lt_impl_le _ _ hab) (lt_impl_le _ _ hxy),
--   have has := le_antisymm _ _ haxby this,
--   clear haxby this,
--   have h1: x * (b - a) + b * (y - x) = 0, {
--     repeat {rw mul_sub},
--     rw has,
--     repeat {rw mul_comm _ x},
--     rw add_comm,
--     change x * a + -(x * b) + (x * b + -(x * a)) = 0,
--     rw add_assoc,
--     rw add_comm,
--     repeat {rw add_assoc},
--     rw neg_add,
--     rw add_zero,
--     rw neg_add,
--   },
--   have h2: 0 ≤ x * (b - a), {
--     rw lt_iff_diff_pos at hab,
--     have := le_mul_comb_nonneg _ _ _ _ (le_refl _) (le_refl _) h0x
--       (lt_impl_le _ _ hab),
--     rw zero_mul at this,
--     assumption,
--   },
--   have h3: 0 < b * (y - x), {
--     rw lt_iff_diff_pos at hxy,
--     from zero_lt_mul _ _ (le_lt_chain _ h0a hab) hxy,
--   },
--   have := lt_le_comb h3 h2,
--   rw add_zero at this,
--   rw add_comm at this,
--   rw h1 at this,
--   from lt_nrefl _ this,
-- end

-- private lemma inv_pos: 0 < a → 0 < a⁻¹ :=
-- begin
--   assume h0x,
--   assume hxi0,
--   by_cases h: 0 ≤ a⁻¹, {
--     have := le_antisymm hxi0 h,
--     have hx0: a = 0, {
--       rw ←@inv_inv a,
--       rw this,
--       refl,
--     },
--     subst hx0,
--     from lt_nrefl _ h0x,
--   }, {
--     rw ←lt_iff_nle at h,
--     rw lt_neg_switch at h,
--     rw neg_zero at h,
--     have := zero_lt_mul _ _ h0x h,
--     rw mul_with_neg at this,
--     rw mul_comm at this,
--     rw inv_self_mul at this,
--     rw lt_neg_switch at this,
--     rw neg_zero at this,
--     rw neg_neg at this,
--     from this zero_le_one,
--     assume hc,
--     from lt_impl_ne h0x hc.symm,
--  },
-- end

-- theorem pos_iff_inv_pos : 0 < a ↔ 0 < a⁻¹ :=
-- begin
--   split, {
--     from inv_pos a,
--   }, {
--     have := inv_pos a⁻¹,
--     rw inv_inv at this,
--     assumption,
--   },
-- end

end ordered_myfield

end hidden