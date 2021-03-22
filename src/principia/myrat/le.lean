import ..myint.le
import .basic
import ..myint.basic
import ..myfield.order

namespace hidden

open myring
open ordered_myring
open ordered_integral_domain

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
    from zero_lt_mul x.denom_pos a.denom_pos,
  },
  rw ←le_mul_cancel_pos_right _ _ (x.denom * a.denom) this,
  conv {
    congr,
    rw mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    rw mul_assoc,
    congr, skip, congr, skip,
    rw mul_comm,
    rw ←hab,
    skip,
    rw mul_comm x.denom,
    rw mul_assoc,
    rw mul_comm,
    rw mul_assoc,
    rw mul_assoc,
    congr, skip, congr, skip,
    rw mul_comm,
    rw ←hxy,
  },
  have hrw: y.denom * (x.denom * (a.num * b.denom)) = y.denom * b.denom * (a.num * x.denom), {
    ac_refl,
  },
  have hrw2: b.denom * (a.denom * (x.num * y.denom)) = y.denom * b.denom * (x.num * a.denom), {
    ac_refl,
  },
  rw hrw,
  rw hrw2,
  apply le_mul_nonneg_left, {
    apply zero_le_mul; apply lt_impl_le, {
      from y.denom_pos,
    }, {
      from b.denom_pos,
    },
  }, {
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

instance decidable_le: ∀ x y: frac, decidable (x ≤ y) :=
λ x y, myint.decidable_le _ _

end frac

namespace myrat

def le := quotient.lift₂ frac.le frac.le_well_defined

instance: has_le myrat := ⟨le⟩
instance has_le2: has_le (quotient frac.frac.setoid) := ⟨le⟩

instance decidable_le: ∀ x y: myrat, decidable (x ≤ y) :=
myint.quotient_decidable_rel frac.le frac.le_well_defined

private theorem le_frac_cls {x y : myrat} {a b : frac} :
(⟦a⟧ ≤ ⟦b⟧ ↔ a ≤ b) := iff.rfl

private theorem le_cls {a b : frac} :
(⟦a⟧ ≤ ⟦b⟧ ↔ a.num * b.denom ≤ b.num * a.denom) :=
iff.rfl

private theorem add_eq_cls {x y: frac}:
⟦x⟧ + ⟦y⟧ = ⟦x + y⟧ := rfl

private theorem mul_eq_cls {x y : frac}:
⟦x⟧ * ⟦y⟧ = ⟦x * y⟧ := rfl

variables x y z : myrat

instance: ordered_myfield myrat := ⟨
  by apply_instance,
  λ x y z: myrat,
  begin
    -- turn into z + x ≤ z + y ↔ x ≤ y for copy/paste purposes
    repeat {rw add_comm _ z},
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    cases quotient.exists_rep z with c hc, subst hc,
    repeat { rw [add_eq_cls, le_cls] },
    repeat { rw frac.add_num <|> rw frac.add_denom, },
    rw [add_mul, add_mul],
    have : c.num * a.denom * (c.denom * b.denom) = c.num * b.denom * (c.denom * a.denom),
      ac_refl,
    rw this, clear this,
    rw ←le_add_cancel_left,
    have : a.num * c.denom * (c.denom * b.denom) = a.num * b.denom * c.denom * c.denom,
      ac_refl,
    rw this, clear this,
    have : b.num * c.denom * (c.denom * a.denom) = b.num * a.denom * c.denom * c.denom,
      ac_refl,
    rw this, clear this,
    rw le_mul_cancel_pos_right _ _ c.denom c.denom_pos,
    rw le_mul_cancel_pos_right _ _ c.denom c.denom_pos,
    from iff.rfl.mp,
    all_goals {apply myint.decidable_eq},
  end,
  λ x y: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    rw mul_eq_cls,
    rw rat_zero,
    repeat {rw le_cls},
    dsimp only [],
    repeat {rw zero_mul <|> rw mul_one},
    from zero_le_mul,
  end,
  λ x y z: myrat,
  begin
    assume hxy hyz,
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    cases quotient.exists_rep z with c hc, subst hc,
    have hxy₁ := le_mul_nonneg_left _ _ _ (lt_impl_le c.denom_pos) hxy,
    have hyz₁ := le_mul_nonneg_left _ _ _ (lt_impl_le a.denom_pos) hyz,
    have : c.denom * (b.num * a.denom) = a.denom * (b.num * c.denom), ac_refl,
    rw this at hxy₁,
    have h : c.denom * (a.num * b.denom) ≤ a.denom * (c.num * b.denom),
      transitivity a.denom * (b.num * c.denom); assumption,
    clear hyz hxy hxy₁ hyz₁ this,
    have : c.denom * (a.num * b.denom) = b.denom * (a.num * c.denom), ac_refl,
    rw this at h, clear this,
    have : a.denom * (c.num * b.denom) = b.denom * (c.num * a.denom), ac_refl,
    rw this at h, clear this,
    rwa le_mul_cancel_pos_left _ _ b.denom b.denom_pos at h,
  end,
  λ x y: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    apply le_total_order,
  end,
  λ x y: myrat,
  begin
    assume hxy hyx,
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    rw le_cls at hxy hyx,
    apply quotient.sound,
    rw frac.setoid_equiv,
    from le_antisymm hxy hyx,
  end⟩

theorem archimedes (x: myrat): ∃ n: myint, x ≤ ↑n :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  existsi abs a.num,
  rw coe_int,
  rw le_cls,
  simp,
  apply le_trans _ (self_le_abs _),
  conv {
    congr,
    rw mul_one,
    rw ←one_mul (abs a.num),
    rw mul_comm,
  },
  apply le_mul_comb_nonneg,
  from abs_nonneg _,
  from myint.le_add_rhs_coe 1 (le_refl _),
  from le_refl _,
  have := a.denom_pos,
  rw myint.lt_iff_succ_le at this,
  from this,
end

end myrat

end hidden
