import ..myint.le
import .add

namespace hidden

namespace frac

def le (x y : frac): Prop :=
x.num * y.denom ≤ y.num * x.denom

instance: has_le frac := ⟨le⟩

theorem le_def (x y: frac):
x ≤ y ↔ x.num * y.denom ≤ y.num * x.denom := iff.rfl

private theorem le_right (a x b y : frac) :
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
      := myint.le_mul_pos
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
      (le_right _ _ _ _ hab hxy)
      (le_right _ _ _ _ (setoid.symm hab) (setoid.symm hxy)),
end

end frac

namespace myrat

def le := quotient.lift₂ (λ x y, x ≤ y) frac.le_well_defined

instance: has_le myrat := ⟨le⟩

end myrat

end hidden
