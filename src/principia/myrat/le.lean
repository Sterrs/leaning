import ..myint.le
import .mul

import ..myint.basic

namespace hidden

namespace frac

def le (x y : frac): Prop :=
x.num * y.denom ≤ y.num * x.denom

instance: has_le frac := ⟨le⟩

theorem le_def (x y: frac):
x ≤ y ↔ x.num * y.denom ≤ y.num * x.denom := iff.rfl

private theorem le_right {a x b y : frac} :
a ≈ b → x ≈ y → (a ≤ x) → (b ≤ y) :=
begin
  assume hab hxy halx,
  rw setoid_equiv at hab,
  rw setoid_equiv at hxy,
  rw le_def,
  rw le_def at halx,
  have : 0 < x.denom * a.denom, {
    from myint.zero_lt_mul _ _ x.denom_pos a.denom_pos,
  },
  rw ←myint.le_mul_cancel_pos_right _ _ _ this,
  conv {
    congr,
    rw myint.mul_assoc,
    rw myint.mul_comm,
    rw myint.mul_assoc,
    rw myint.mul_assoc,
    congr, skip, congr, skip,
    rw myint.mul_comm,
    rw ←hab,
    skip,
    rw @myint.mul_comm x.denom,
    rw myint.mul_assoc,
    rw myint.mul_comm,
    rw myint.mul_assoc,
    rw myint.mul_assoc,
    congr, skip, congr, skip,
    rw myint.mul_comm,
    rw ←hxy,
  },
  have
    := myint.le_mul_nonneg
        (myint.lt_imp_le (myint.zero_lt_mul y.denom_pos b.denom_pos))
        halx,
  have hrw: y.denom * (x.denom * (a.num * b.denom)) = y.denom * b.denom * (a.num * x.denom), {
    ac_refl,
  },
  have hrw2: b.denom * (a.denom * (x.num * y.denom)) = y.denom * b.denom * (x.num * a.denom), {
    ac_refl,
  },
  rw hrw,
  rw hrw2,
  assumption,
end

theorem le_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → (a ≤ x) = (b ≤ y) :=
begin
  assume hab hxy,
  apply propext,
  from
    iff.intro
      (le_right hab hxy)
      (le_right (setoid.symm hab) (setoid.symm hxy)),
end

instance decidable_le: ∀ x y: frac, decidable (x ≤ y) :=
λ x y, myint.decidable_le _ _

end frac

namespace myrat

def le := quotient.lift₂ frac.le frac.le_well_defined

instance: has_le myrat := ⟨le⟩

instance decidable_le: ∀ x y: myrat, decidable (x ≤ y) :=
myint.quotient_decidable_rel frac.le frac.le_well_defined

-- Use Izaak's enormous-brain workaround

theorem le_frac_cls {x y : myrat} {a b : frac} :
x = ⟦a⟧ → y = ⟦b⟧ → (x ≤ y ↔ a ≤ b) :=
λ hxa hyb, by rw [hxa, hyb]; refl

theorem le_cls {x y : myrat} {a b : frac} :
x = ⟦a⟧ → y = ⟦b⟧ → (x ≤ y ↔ a.num * b.denom ≤ b.num * a.denom) :=
λ hxa hyb, by rw [le_frac_cls hxa hyb]; refl

variables x y z : myrat

theorem zero_le_one : (0 : myrat) ≤ 1 :=
begin
  rw [rat_zero, rat_one, le_cls rfl rfl],
  dsimp only [],
  rw [myint.zero_mul, myint.one_mul],
  from myint.zero_le_one,
end

@[refl]
theorem le_refl : x ≤ x :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  rw le_cls rfl rfl,
end

@[trans]
theorem le_trans : x ≤ y → y ≤ z → x ≤ z :=
begin
  assume hxy hyz,
  cases quotient.exists_rep x with a ha, subst ha,
  cases quotient.exists_rep y with b hb, subst hb,
  cases quotient.exists_rep z with c hc, subst hc,
  rw le_cls rfl rfl at hxy hyz ⊢,
  have hxy₁ := myint.le_mul_nonneg (myint.lt_imp_le c.denom_pos) hxy,
  have hyz₁ := myint.le_mul_nonneg (myint.lt_imp_le a.denom_pos) hyz,
  have : c.denom * (b.num * a.denom) = a.denom * (b.num * c.denom), ac_refl,
  rw this at hxy₁,
  have h : c.denom * (a.num * b.denom) ≤ a.denom * (c.num * b.denom),
    transitivity a.denom * (b.num * c.denom); assumption,
  clear hyz hxy hxy₁ hyz₁ this,
  have : c.denom * (a.num * b.denom) = b.denom * (a.num * c.denom), ac_refl,
  rw this at h, clear this,
  have : a.denom * (c.num * b.denom) = b.denom * (c.num * a.denom), ac_refl,
  rw this at h, clear this,
  rwa myint.le_mul_cancel_pos_left b.denom_pos at h,
end

theorem le_cancel_left {x y z : myrat} : z + x ≤ z + y ↔ x ≤ y :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  cases quotient.exists_rep y with b hb, subst hb,
  cases quotient.exists_rep z with c hc, subst hc,
  repeat { rw [add_eq_cls rfl rfl, le_cls rfl rfl] },
  repeat { rw frac.add_num <|> rw frac.add_denom, },
  rw [myint.add_mul, myint.add_mul],
  have : c.num * a.denom * (c.denom * b.denom) = c.num * b.denom * (c.denom * a.denom),
    ac_refl,
  rw this, clear this,
  rw myint.le_cancel_left,
  have : a.num * c.denom * (c.denom * b.denom) = a.num * b.denom * c.denom * c.denom,
    ac_refl,
  rw this, clear this,
  have : b.num * c.denom * (c.denom * a.denom) = b.num * a.denom * c.denom * c.denom,
    ac_refl,
  rw this, clear this,
  repeat { rwa myint.le_mul_cancel_pos_right c.denom_pos, },
end

theorem le_add_left {x y : myrat} (z : myrat) : x ≤ y ↔ z + x ≤ z + y :=
le_cancel_left.symm

theorem le_cancel_right {x y z : myrat} : x + z ≤ y + z ↔ x ≤ y :=
by rw [add_comm, add_comm y]; from le_cancel_left

theorem le_add_right {x y : myrat} (z : myrat) : x ≤ y ↔ x + z ≤ y + z :=
le_cancel_right.symm

theorem le_comb {a b : myrat} {x y : myrat} : a ≤ b → x ≤ y → a + x ≤ b + y :=
begin
  assume hab hxy,
  rw le_add_right x at hab,
  rw le_add_left b at hxy,
  transitivity b + x; assumption,
end

private lemma le_neg_switch_right: x ≤ y → -y ≤ -x :=
begin
  assume hxy,
  rw le_add_right (x + y),
  conv {
    congr,
    rw add_comm x,
    rw ←add_assoc,
    rw neg_self_add,
    rw zero_add,
    skip,
    rw ←add_assoc,
    rw neg_self_add,
    rw zero_add,
  },
    assumption,
end

theorem le_neg_switch: x ≤ y ↔ -y ≤ -x :=
begin
  apply iff.intro (le_neg_switch_right _ _),
  assume hyx,
  rw ←neg_neg x,
  rw ←neg_neg y,
  from le_neg_switch_right _ _ hyx,
end

theorem le_total_order : x ≤ y ∨ y ≤ x :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  cases quotient.exists_rep y with b hb, subst hb,
  rw [le_cls rfl rfl, le_cls rfl rfl],
  from myint.le_total_order (a.num * b.denom) (b.num * a.denom),
end

theorem le_mul_nonneg_left {x y z : myrat} : 0 ≤ z → x ≤ y → z * x ≤ z * y :=
begin
  assume h0z hxy,
  cases quotient.exists_rep x with a ha, subst ha,
  cases quotient.exists_rep y with b hb, subst hb,
  cases quotient.exists_rep z with c hc, subst hc,
  rw mul_eq_cls rfl rfl,
  rw mul_eq_cls rfl rfl,
  rw le_cls rfl rfl,
  repeat {rw frac.mul_num <|> rw frac.mul_denom},
  cases hcn: c.num with cn cn, {
    rw le_cls rfl rfl at hxy,
    conv {
      congr,
      rw myint.mul_assoc,
      congr,
      skip,
      rw myint.mul_comm,
      rw myint.mul_assoc,
      congr,
      skip,
      rw myint.mul_comm,
      skip,
      rw myint.mul_assoc,
      congr,
      skip,
      rw myint.mul_comm,
      rw myint.mul_assoc,
      congr,
      skip,
      rw myint.mul_comm,
    },
    conv {
      congr,
      rw ←myint.mul_assoc,
      skip,
      rw ←myint.mul_assoc,
    },
    apply myint.le_mul_nonneg, {
      rw ←@myint.mul_zero (myint.of_nat cn),
      apply myint.le_mul_nonneg, {
        rw ←myint.coe_nat_eq,
        -- ???
        have: (0: myint) = (0: mynat) := rfl,
        rw this,
        rw myint.nat_nat_le,
        from mynat.zero_le,
      }, {
        from myint.lt_imp_le (c.denom_pos),
      },
    }, {
      assumption,
    },
  }, {
    exfalso,
    rw rat_zero at h0z,
    rw le_cls rfl rfl at h0z,
    simp at h0z,
    rw myint.zero_mul at h0z,
    rw myint.mul_one at h0z,
    rw hcn at h0z,
    have: (0: myint) = (0: mynat) := rfl,
    rw this at h0z,
    from myint.nat_neg_le h0z,
  },
end

theorem le_mul_nonneg_right {x y z : myrat} : 0 ≤ z → x ≤ y → x * z ≤ y * z :=
λ hc hab, by rw [mul_comm, mul_comm y]; from le_mul_nonneg_left hc hab

theorem le_mul_comb_nonneg {x y z w : myrat}
(hx : 0 ≤ x) (hz : 0 ≤ z) (hxy : x ≤ y) (hzw : z ≤ w) :
 x * z ≤ y * w :=
begin
  transitivity (y * z),
    apply le_mul_nonneg_right; assumption,
  apply le_mul_nonneg_left,
    transitivity x; assumption,
  assumption,
end

theorem le_mul_nonpos_left {x y z : myrat} : z ≤ 0 → x ≤ y → z * y ≤ z * x :=
begin
  assume hz0 hxy,
  rw le_neg_switch at hz0,
  rw le_neg_switch at hxy,
  have := le_mul_nonneg_left hz0 hxy,
  repeat {rw mul_neg_neg at this},
  assumption,
end

theorem le_mul_nonpos_right {x y z : myrat} : z ≤ 0 → x ≤ y → y * z ≤ x * z :=
λ hc hab, by rw [mul_comm, mul_comm x]; from le_mul_nonpos_left hc hab

theorem le_antisymm {x y : myrat} : x ≤ y → y ≤ x → x = y := sorry

theorem square_nonneg : 0 ≤ x * x :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  rw mul_eq_cls rfl rfl,
  rw rat_zero,
  rw le_cls rfl rfl,
  simp,
  rw myint.zero_mul,
  rw myint.mul_one,
  rw frac.mul_num,
  from myint.square_non_neg _,
end

theorem abs_nonneg : 0 ≤ abs x :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  rw rat_zero,
  rw abs_eq_cls rfl,
  rw le_cls rfl rfl,
  simp,
  rw myint.zero_mul,
  rw myint.mul_one,
  rw frac.abs_num,
  from myint.zero_is_le_abs,
end

theorem triangle_ineq : abs (x + y) ≤ abs x + abs y :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  cases quotient.exists_rep y with b hb, subst hb,
  repeat {rw abs_eq_cls rfl <|> rw add_eq_cls rfl rfl},
  rw le_cls rfl rfl,
  repeat {rw frac.add_denom <|> rw frac.add_num <|> rw frac.abs_denom},
  repeat {rw ←@myint.mul_comm (a.denom * b.denom)},
  apply myint.le_mul_nonneg, {
    rw ←myint.mul_zero,
    from myint.le_mul_nonneg
      (myint.lt_imp_le a.denom_pos)
      (myint.lt_imp_le b.denom_pos),
  }, {
    repeat {rw frac.abs_num},
    rw frac.add_num,
    conv {
      to_rhs,
      congr, congr, skip,
      rw myint.zero_le_abs (myint.lt_imp_le b.denom_pos),
      skip, congr, skip,
      rw myint.zero_le_abs (myint.lt_imp_le a.denom_pos),
    },
    repeat {rw myint.abs_distr_int},
    from myint.triangle_ineq_int,
  },
end

theorem archimedes (x: myrat): ∃ n: myint, x ≤ ↑n :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  cases han: a.num with an an, {
    existsi myint.of_nat an,
    rw coe_int,
    rw le_cls rfl rfl,
    simp,
    rw han,
    rw myint.mul_one,
    rw myint.zero_le_abs (myint.lt_imp_le a.denom_pos),
    rw ←myint.coe_nat_eq,
    rw myint.nat_nat_mul,
    rw myint.nat_nat_le,
    rw mynat.mul_comm,
    apply @mynat.le_rhs_mul an an a.denom.abs _ mynat.le_refl,
    -- maybe lemma somewhere else
    cases had: a.denom with ad ad, {
      cases ad with ad, {
        have := a.denom_pos,
        rw had at this,
        exfalso,
        from myint.lt_nrefl this,
      }, {
        assume h,
        cases h,
      },
    }, {
      assume h,
      cases h,
    },
  }, {
    existsi (0: myint),
    rw coe_int,
    rw le_cls rfl rfl,
    simp,
    rw myint.mul_one,
    rw myint.zero_mul,
    rw han,
    from myint.neg_nat_le,
  },
end

end myrat

end hidden
