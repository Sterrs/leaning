import .le
import .mul

namespace hidden

namespace myrat

def lt (x y : myrat) := ¬y ≤ x

instance: has_lt myrat := ⟨lt⟩

instance decidable_lt: ∀ x y: myrat, decidable (x < y) :=
λ x y, not.decidable

variables x y z : myrat

theorem lt_iff_nle : x < y ↔ ¬y ≤ x := iff.rfl

theorem lt_impl_ne {x y : myrat} : x < y → x ≠ y :=
begin
  assume hxy hxeqy,
  subst hxeqy,
  apply hxy,
  refl,
end

theorem lt_nrefl: ¬(x < x) :=
begin
  assume h,
  from lt_impl_ne h rfl,
end

theorem lt_impl_le: x < y → x ≤ y :=
begin
  assume hxy,
  cases le_total_order x y with h h, {
    assumption,
  }, {
    contradiction,
  },
end

theorem lt_very_antisymmetric: ¬(x < y ∧ y < x) :=
begin
  assume h,
  cases h with hxy hyx,
  cases le_total_order x y; contradiction,
end

theorem lt_neg_switch: x < y ↔ -y < -x :=
iff_to_contrapositive (le_neg_switch y x)

@[trans]
theorem lt_trans {a b c : myrat} : a < b → b < c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ _ _ (lt_impl_le _ _ hab) (lt_impl_le _ _ hbc),
  have h := le_antisymm hac this,
  subst h,
  from lt_very_antisymmetric _ _ ⟨hbc, hab⟩,
end

theorem zero_lt_mul (a b: myrat): 0 < a → 0 < b → 0 < a * b :=
begin
  assume hapos hbpos,
  assume hab0,
  have := le_mul_nonneg_right (lt_impl_le _ _ hapos) (lt_impl_le _ _ hbpos),
  rw zero_mul at this,
  rw mul_comm at this,
  have h0 := le_antisymm hab0 this,
  cases (mul_integral h0) with ha hb,
  have hc := lt_impl_ne hapos,
  from hc ha.symm,
  have hc := lt_impl_ne hbpos,
  from hc hb.symm,
end

theorem lt_cancel_left {a b c : myrat} : c + a < c + b ↔ a < b :=
iff_to_contrapositive le_cancel_left

theorem lt_add_left {a b : myrat} (c : myrat) : a < b ↔ c + a < c + b :=
lt_cancel_left.symm

theorem lt_cancel_right {a b c : myrat} : a + c < b + c ↔ a < b :=
by rw [add_comm, add_comm b]; from lt_cancel_left

theorem lt_add_right {a b : myrat} (c : myrat) : a < b ↔ a + c < b + c :=
lt_cancel_right.symm

theorem lt_rearrange: x < y ↔ 0 < y - x :=
begin
  have := @lt_cancel_right x y (-x),
  simp at this,
  symmetry,
  from this,
end

theorem lt_mul_pos_right {z : myrat} : 0 < z → ∀ x y : myrat, x < y ↔ x * z < y * z :=
begin
  assume h0z,
  intros x y,
  split; assume h, {
    rw lt_rearrange,
    rw lt_rearrange at h,
    rw ←sub_mul,
    from zero_lt_mul _ _ h h0z,
  }, {
    rw lt_rearrange,
    rw lt_rearrange at h,
    assume h0yx,
    rw ←sub_mul at h,
    by_cases h1: 0 ≤ y - x, {
      have := le_antisymm h0yx h1,
      rw this at h,
      rw zero_mul at h,
      from lt_nrefl _ h,
    }, {
      rw ←lt_iff_nle at h1,
      rw lt_rearrange at h1,
      have := zero_lt_mul _ _ h1 h0z,
      rw zero_sub at this,
      rw lt_neg_switch at this,
      rw mul_neg_with at this,
      rw neg_neg at this,
      rw neg_zero at this,
      from lt_very_antisymmetric _ _ ⟨this, h⟩,
    },
  },
end

theorem lt_mul_pos_left {z : myrat} : 0 < z → ∀ x y : myrat, x < y ↔ z * x < z * y :=
begin
  assume h0z,
  intros x y,
  repeat {rw mul_comm z},
  from lt_mul_pos_right h0z x y,
end

theorem lt_comb {a b c d: myrat}: a < b → c < d → a + c < b + d :=
begin
  assume hab hcd,
  transitivity a + d,
  rw ←lt_add_left,
  assumption,
  rw ←lt_add_right,
  assumption,
end

-- It's debatable whether these should have b as an implicit or explicit
-- argument. When used like `transitivity`, by `apply`ing it, we need to supply
-- which middle term we are using.
-- However, in all other use cases we would supply both hypotheses.
-- Personally, I think `apply`ing these theorems should be the standard way to
-- use them as it involves the least `have` statements, resulting in shorter proofs
-- with fewer labels used (so no h, h₁, h₂, hxy, hxy₁ etc.)

theorem lt_le_chain {a c: myrat} (b : myrat): a < b → b ≤ c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ _ _ (lt_impl_le _ _ hab) hbc,
  have h := le_antisymm this hac,
  subst h,
  clear hac this,
  have := le_antisymm (lt_impl_le _ _ hab) hbc,
  subst this,
  from lt_nrefl _ hab,
end

theorem le_lt_chain {a c: myrat} (b : myrat): a ≤ b → b < c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ _ _ hab (lt_impl_le _ _ hbc),
  have h := le_antisymm this hac,
  subst h,
  clear hac this,
  have := le_antisymm (lt_impl_le _ _ hbc) hab,
  subst this,
  from lt_nrefl _ hbc,
end

theorem lt_le_comb {a b c d: myrat}: a < b → c ≤ d → a + c < b + d :=
begin
  assume hab hcd,
  apply le_lt_chain (a + d),
  rw ←le_add_left,
  assumption,
  rw ←lt_add_right,
  assumption,
end

theorem abs_lt (a b : myrat) : abs a < b ↔ -b < a ∧ a < b :=
begin
  split; assume h, {
    split, {
      rw lt_neg_switch,
      rw neg_neg,
      apply le_lt_chain a.abs, {
        rw ←abs_neg,
        from le_self_abs _,
      }, {
        assumption,
      },
    }, {
      apply le_lt_chain a.abs, {
        from le_self_abs _,
      }, {
        assumption,
      },
    },
  }, {
    cases h with hba hab,
    rw lt_neg_switch at hba,
    rw neg_neg at hba,
    cases (@abs_plusminus a) with h h, {
      rw h,
      assumption,
    }, {
      rw h,
      assumption,
    },
  },
end

theorem abs_lt_left {a b : myrat} : abs a < b → -b < a :=
λ h, by rw abs_lt at h; from h.left

theorem abs_lt_right {a b : myrat} : abs a < b → a < b :=
λ h, by rw abs_lt at h; from h.right

theorem lt_abs {a b : myrat} : a < abs b → b < -a ∨ a < b :=
begin
  assume hab,
  cases @abs_plusminus b with h h, {
    rw ←h,
    right, assumption,
  }, {
    left,
    rw lt_neg_switch,
    rw neg_neg,
    rw ←h,
    assumption,
  },
end

-- abs_diff refers to the pattern `abs (a - b) < c` which often shows up in analysis

theorem abs_diff_lt_left {a b c : myrat} : abs (a - b) < c → b - c < a :=
begin
  assume h,
  have h₁ := abs_lt_left h,
  rwa [lt_add_right b, ←sub_add_neg, add_assoc, neg_self_add,
       add_zero, add_comm, sub_add_neg] at h₁,
end

theorem abs_diff_lt_right {a b c : myrat} : abs (a - b) < c → a < b + c :=
begin
  assume h,
  have h₁ := abs_lt_right h,
  rwa [lt_add_right b, ←sub_add_neg, add_assoc, neg_self_add,
       add_zero, add_comm] at h₁,
end

theorem zero_lt_one : (0 : myrat) < 1 :=
begin
  assume h,
  from one_nzero (le_antisymm h zero_le_one),
end

theorem zero_lt_two : (0 : myrat) < 2 :=
begin
  rw [←one_plus_one, ←zero_add (0 : myrat)],
  apply @lt_comb 0 1 0 1; from zero_lt_one,
end

theorem half_pos {ε : myrat} : 0 < ε → 0 < ε / 2 :=
assume h, by rwa [lt_mul_pos_right zero_lt_two, zero_mul, div_mul_cancel two_nzero]

theorem exists_between (a c : myrat) :
a < c → ∃ b : myrat, a < b ∧ b < c :=
begin
  assume hac,
  existsi (a + c) / 2,
  split; rw add_div, {
    rw [lt_add_left (-(a/2)), ←add_assoc, add_comm _ a, neg_self_add],
    conv {
      to_lhs,
      congr,
        rw ←@half_plus_half a, skip,
      skip,
    },
    rw [add_assoc, self_neg_add, add_zero, zero_add],
    rwa [lt_mul_pos_right zero_lt_two, div_mul_cancel two_nzero,
         div_mul_cancel two_nzero],
  }, {
    rw [lt_add_right (-(c / 2)), add_assoc, self_neg_add],
    conv {
      to_rhs,
      congr,
        rw ←@half_plus_half c, skip,
      skip,
    },
    rw [add_assoc, self_neg_add, add_zero, add_zero],
    rwa [lt_mul_pos_right zero_lt_two, div_mul_cancel two_nzero,
         div_mul_cancel two_nzero],
  },
end

theorem lt_mul_comb_nonneg {a b x y : myrat} : 0 ≤ a → 0 ≤ x → a < b → x < y → a * x < b * y :=
begin
  assume h0a h0x hab hxy haxby,
  have := le_mul_comb_nonneg h0a h0x
    (lt_impl_le _ _ hab) (lt_impl_le _ _ hxy),
  have has := le_antisymm haxby this,
  clear haxby this,
  have h1: x * (b - a) + b * (y - x) = 0, {
    repeat {rw mul_sub},
    rw has,
    repeat {rw mul_comm _ x},
    repeat {rw ←sub_add_neg},
    rw add_comm,
    rw add_assoc,
    rw add_comm,
    repeat {rw add_assoc},
    rw neg_self_add,
    rw add_zero,
    rw neg_self_add,
  },
  have h2: 0 ≤ x * (b - a), {
    rw lt_rearrange at hab,
    have := le_mul_comb_nonneg (le_refl _) (le_refl _) h0x
      (lt_impl_le _ _ hab),
    rw zero_mul at this,
    assumption,
  },
  have h3: 0 < b * (y - x), {
    rw lt_rearrange at hxy,
    from zero_lt_mul _ _ (le_lt_chain _ h0a hab) hxy,
  },
  have := lt_le_comb h3 h2,
  rw add_zero at this,
  rw add_comm at this,
  rw h1 at this,
  from lt_nrefl _ this,
end

private lemma inv_pos: 0 < x → 0 < x⁻¹ :=
begin
  assume h0x,
  assume hxi0,
  by_cases h: 0 ≤ x⁻¹, {
    have := le_antisymm hxi0 h,
    have hx0: x = 0, {
      rw ←@inv_inv x,
      rw this,
      refl,
    },
    subst hx0,
    from lt_nrefl _ h0x,
  }, {
    rw ←lt_iff_nle at h,
    rw lt_neg_switch at h,
    rw neg_zero at h,
    have := zero_lt_mul _ _ h0x h,
    rw mul_with_neg at this,
    rw mul_comm at this,
    rw inv_self_mul at this,
    rw lt_neg_switch at this,
    rw neg_zero at this,
    rw neg_neg at this,
    from this zero_le_one,
    assume hc,
    from lt_impl_ne h0x hc.symm,
 },
end

theorem pos_iff_inv_pos : 0 < x ↔ 0 < x⁻¹ :=
begin
  split, {
    from inv_pos x,
  }, {
    have := inv_pos x⁻¹,
    rw inv_inv at this,
    assumption,
  },
end

theorem le_iff_lt_or_eq: x ≤ y ↔ x < y ∨ x = y :=
begin
  split, {
    assume hxy,
    by_cases h: y ≤ x, {
      right,
      from  le_antisymm hxy h,
    }, {
      left,
      assumption,
    },
  }, {
    assume h,
    cases h with h1 h2, {
      from lt_impl_le _ _ h1,
    }, {
      rw h2,
    },
  },
end

theorem lt_trichotomy: x = y ∨ x < y ∨ y < x :=
begin
  by_cases h: x ≤ y, {
    rw le_iff_lt_or_eq at h,
    cases h with h h, {
      right, left, assumption,
    }, {
      left, assumption,
    },
  }, {
    right, right, assumption,
  },
end

-- basically de Morgan
theorem lt_iff_le_and_neq: x < y ↔ x ≤ y ∧ x ≠ y :=
begin
  split, {
    assume h,
    split, {
      from lt_impl_le _ _ h,
    }, {
      from lt_impl_ne h,
    },
  }, {
    assume h,
    rw le_iff_lt_or_eq at h,
    cases h with h1 h2,
    cases h1 with h h, {
      assumption,
    }, {
      contradiction,
    },
  },
end

end myrat

end hidden
