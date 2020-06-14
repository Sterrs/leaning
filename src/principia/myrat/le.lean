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

variables a b c : myrat

@[refl]
theorem le_refl : a ≤ a := sorry
@[trans]
theorem le_trans : a ≤ b → b ≤ c → a ≤ c := sorry

theorem le_cancel_left {a b c : myrat} : c + a ≤ c + b ↔ a ≤ b := sorry

theorem le_add_left {a b : myrat} (c : myrat) : a ≤ b ↔ c + a ≤ c + b :=
le_cancel_left.symm

theorem le_cancel_right {a b c : myrat} : a + c ≤ b + c ↔ a ≤ b :=
by rw [add_comm, add_comm b]; from le_cancel_left

theorem le_add_right {a b : myrat} (c : myrat) : a ≤ b ↔ a + c ≤ b + c :=
le_cancel_right.symm

theorem le_neg_switch : a ≤ b ↔ -b ≤ -a := sorry

theorem le_comb {a b : myrat} {x y : myrat} : a ≤ b → x ≤ y → a + x ≤ b + y := sorry

theorem le_total_order : a ≤ b ∨ b ≤ a := sorry

theorem le_mul_nonneg_left {a b c : myrat} : 0 ≤ c → a ≤ b → c * a ≤ c * b := sorry

theorem le_mul_nonneg_right {a b c : myrat} : 0 ≤ c → a ≤ b → a * c ≤ b * c :=
λ hc hab, by rw [mul_comm, mul_comm b]; from le_mul_nonneg_left hc hab

theorem le_mul_nonpos_left {a b c : myrat} : c ≤ 0 → a ≤ b → c * b ≤ c * a := sorry

theorem le_mul_nonpos_right {a b c : myrat} : c ≤ 0 → a ≤ b → b * c ≤ a * c :=
λ hc hab, by rw [mul_comm, mul_comm a]; from le_mul_nonpos_left hc hab

theorem le_antisymm {a b : myrat} : a ≤ b → b ≤ a → a = b := sorry

theorem square_nonneg : 0 ≤ a * a := sorry

-- {a b c : myrat}

theorem triangle_ineq (a b: myrat): abs (a + b) ≤ abs a + abs b :=
begin
    sorry,
end

end myrat

end hidden
