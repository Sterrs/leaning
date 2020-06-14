import ..myint.le
import .mul

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
  apply @myint.le_mul_cancel_pos _ _ (x.denom * a.denom), {
    from myint.zero_lt_mul x.denom_pos a.denom_pos,
  }, {
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
  },
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

end frac

namespace myrat

def le := quotient.lift₂ (λ x y, x ≤ y) frac.le_well_defined

instance: has_le myrat := ⟨le⟩

-- Use Izaak's enormous-brain workaround

theorem le_frac_cls {x y : myrat} {a b : frac} :
x = ⟦a⟧ → y = ⟦b⟧ → (x ≤ y ↔ a ≤ b) :=
λ hxa hyb, by rw [hxa, hyb]; refl

theorem le_cls {x y : myrat} {a b : frac} :
x = ⟦a⟧ → y = ⟦b⟧ → (x ≤ y ↔ a.num * b.denom ≤ b.num * a.denom) :=
λ hxa hyb, by rw [le_frac_cls hxa hyb]; refl

variables x y z : myrat

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

theorem le_neg_switch : x ≤ y ↔ -y ≤ -x := sorry

theorem le_comb {a b : myrat} {x y : myrat} : a ≤ b → x ≤ y → a + x ≤ b + y :=
begin
  assume hab hxy,
  rw le_add_right x at hab,
  rw le_add_left b at hxy,
  transitivity b + x; assumption,
end

theorem le_total_order : x ≤ y ∨ y ≤ x := sorry

theorem le_mul_nonneg_left {x y z : myrat} : 0 ≤ z → x ≤ y → z * x ≤ z * y := sorry

theorem le_mul_nonneg_right {x y z : myrat} : 0 ≤ z → x ≤ y → x * z ≤ y * z :=
λ hc hab, by rw [mul_comm, mul_comm y]; from le_mul_nonneg_left hc hab

theorem le_mul_nonpos_left {x y z : myrat} : z ≤ 0 → x ≤ y → z * y ≤ z * x := sorry

theorem le_mul_nonpos_right {x y z : myrat} : z ≤ 0 → x ≤ y → y * z ≤ x * z :=
λ hc hab, by rw [mul_comm, mul_comm x]; from le_mul_nonpos_left hc hab

theorem le_antisymm {x y : myrat} : x ≤ y → y ≤ x → x = y := sorry

theorem square_nonneg : 0 ≤ x * x := sorry

theorem triangle_ineq : abs (x + y) ≤ abs x + abs y :=
begin
    sorry,
end

end myrat

end hidden
