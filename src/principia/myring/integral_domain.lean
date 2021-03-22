import .order
#check le_antisymm
namespace hidden

-- nontriviality axiom?
class integral_domain (α : Type) extends myring α :=
(mul_integral_left (a b : α) : a ≠ 0 → b * a = 0 → b = 0)

namespace integral_domain

variables {α : Type} [integral_domain α]
variables (a b c : α)

theorem mul_integral_right : a ≠ 0 → a * b = 0 → b = 0 :=
begin
  assume ha h,
  apply mul_integral_left a _,
    assumption,
  rwa myring.mul_comm,
end

-- This requires decidability
theorem mul_integral : a * b = 0 → a = 0 ∨ b = 0 :=
begin
  assume hab,
  by_cases a = 0,
    left, assumption,
  right,
  apply mul_integral_right a; assumption,
end

theorem mul_nzero {a b : α}: a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
  intros ha hb hab,
  apply ha,
  apply mul_integral_left b; assumption,
end

theorem mul_cancel_right : b ≠ 0 → a * b = c * b → a = c :=
begin
  assume hb h,
  rw ←myring.sub_to_zero_iff_eq at ⊢ h,
  rw ←myring.sub_mul at h,
  apply mul_integral_left b _ hb h,
end

theorem mul_cancel_left : a ≠ 0 → a * b = a * c → b = c :=
begin
  assume ha h,
  apply mul_cancel_right _ a _,
    assumption,
  rwa [myring.mul_comm a, myring.mul_comm a] at h,
end

end integral_domain

-- If this breaks everything I'm sorry
-- set_option old_structure_cmd true

class ordered_integral_domain (α : Type) extends integral_domain α, has_le α :=
-- NOTE: Theses are the ordered_myring axioms
-- NOTE: Added `oid_` to avoid name clash when opening alongside ordered_myring
(oid_decidable_le: ∀ a b: α, decidable (a ≤ b))
(oid_le_add_right (a b c : α) : a ≤ b → a + c ≤ b + c)
(oid_zero_le_mul (a b : α) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
(oid_le_trans (a b c: α): a ≤ b → b ≤ c → a ≤ c)
(oid_le_total_order (a b: α): a ≤ b ∨ b ≤ a)
(oid_le_antisymm (a b: α): a ≤ b → b ≤ a → a = b)

namespace ordered_integral_domain

variables {α : Type} [ordered_integral_domain α] (a b c : α)

instance : ordered_myring α := {
  decidable_le := oid_decidable_le,
  le_add_right := oid_le_add_right,
  zero_le_mul := oid_zero_le_mul,
  le_trans := oid_le_trans,
  le_total_order := oid_le_total_order,
  le_antisymm := oid_le_antisymm,
}

open myring
open ordered_myring
open integral_domain

-- only works in ordered integral domain
-- (consider lexicographic order on ℤ × ℤ)
theorem zero_lt_mul {a b : α} : 0 < a → 0 < b → 0 < a * b :=
begin
  assume hapos hbpos,
  assume hab0,
  have := le_mul_nonneg_right _ _ _ (lt_impl_le _ a hapos) (lt_impl_le _ _ hbpos),
  rw zero_mul at this,
  rw mul_comm at this,
  have h0 := le_antisymm _ _ hab0 this,
  cases (mul_integral _ _ h0) with ha hb,
  have hc := lt_impl_ne _ _ hapos,
  from hc ha.symm,
  have hc := lt_impl_ne _ _ hbpos,
  from hc hb.symm,
end

theorem lt_mul_pos_right : 0 < c → ∀ a b: α, a < b ↔ a * c < b * c :=
begin
  assume h0z,
  intros a b,
  split; assume h, {
    rw lt_iff_diff_pos,
    rw lt_iff_diff_pos at h,
    rw ←sub_mul,
    apply zero_lt_mul; assumption,
  }, {
    rw lt_iff_diff_pos,
    rw lt_iff_diff_pos at h,
    assume h0yx,
    rw ←sub_mul at h,
    cases le_total_order c 0 with hc hc, {
      contradiction,
    }, {
      apply h,
      rw le_neg_switch_iff,
      rw neg_zero,
      rw ←neg_mul,
      apply zero_le_mul, {
        rw le_neg_switch_iff at h0yx,
        rw neg_zero at h0yx,
        assumption,
      }, {
        assumption,
      },
    },
  },
end

theorem lt_mul_pos_left :
0 < c → ∀ a b : α, a < b ↔ c * a < c * b :=
begin
  assume h0z,
  intros a b,
  repeat {rw mul_comm c},
  apply lt_mul_pos_right,
  assumption,
end

-- this one needs integral domain assumptions
-- slicker proof welcomed
private lemma sign_mul_half (h0a: 0 < a):
sign (a * b) = sign a * sign b :=
begin
  rw sign_of_pos _ h0a,
  by_cases h0b: 0 < b, {
    rw sign_of_pos _ h0b,
    rw sign_of_pos _ (zero_lt_mul h0a h0b),
    rw mul_one,
  }, {
    by_cases hb0: b < 0, {
      rw sign_of_neg _ hb0,
      rw lt_zero_neg_switch_iff at hb0,
      rw neg_eq,
      rw ←sign_neg,
      rw ←mul_neg,
      rw sign_of_pos _ (zero_lt_mul h0a hb0), {
        rw mul_neg,
        rw neg_neg,
        rw mul_one,
      },
    }, {
      suffices h: b = 0, {
        rw h,
        repeat {rw mul_zero <|> rw sign_zero},
      }, {
        apply ordered_myring.le_antisymm, {
          from decidable.of_not_not h0b,
        }, {
          from decidable.of_not_not hb0,
        },
      },
    },
  },
end

theorem sign_mul : sign (a * b) = sign a * sign b :=
begin
  by_cases h0a: 0 < a, {
    from sign_mul_half _ _ h0a,
  }, {
    by_cases ha0: a < 0, {
      rw lt_zero_neg_switch_iff at ha0,
      have := sign_mul_half (-a) b ha0, {
        rw neg_mul at this,
        repeat {rw sign_neg at this},
        rw neg_mul at this,
        rw ←neg_eq at this,
        from this,
      },
    }, {
      suffices h: a = 0, {
        rw h,
        repeat {rw zero_mul <|> rw sign_zero},
      }, {
        apply ordered_myring.le_antisymm, {
          from decidable.of_not_not h0a,
        }, {
          from decidable.of_not_not ha0,
        },
      }
    },
  },
end

theorem le_mul_cancel_pos_right : 0 < c → (a * c ≤ b * c ↔ a ≤ b) :=
begin
  assume hc,
  split; assume h, {
    sorry,
  }, {
    sorry,
  },
end

theorem le_mul_cancel_pos_left : 0 < c → (c * a ≤ c * b ↔ a ≤ b) :=
begin
  rw [mul_comm, mul_comm c],
  exact le_mul_cancel_pos_right _ _ _,
end

theorem lt_mul_comb_nonneg {a b c d : α}
(hx : 0 ≤ a) (hz : 0 ≤ c) (hxy : a < b) (hzw : c < d):
 a * c < b * d :=
begin
  sorry,
end

end ordered_integral_domain

end hidden
