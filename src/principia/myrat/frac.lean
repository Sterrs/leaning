import ..myint.lt
import ..myint.max

namespace hidden

open myint

structure frac :=
-- Numerator
(num : myint)
-- Denominator
(denom : myint)
-- Proof that the denominator is positive
(denom_pos : 0 < denom)

namespace frac

variables {x y z : frac}

-- Is this really necessary?
theorem num_and_denom_eq : x = y ↔ x.num = y.num ∧ x.denom = y.denom :=
begin
  split; assume h, {
    split,
    all_goals { congr, assumption, },
  }, {
    cases x,
    cases y,
    dsimp only [] at h,
    cases h with hnum hdenom,
    subst hnum,
    subst hdenom, -- Magic?
  },
end

def frac_eq (x y : frac):
Prop := x.num * y.denom = y.num * x.denom

private theorem frac_eq_refl : reflexive frac_eq :=
begin
  intro x,
  unfold frac_eq,
end

private theorem frac_eq_symm : symmetric frac_eq :=
begin
  intros x y,
  assume h,
  from h.symm,
end

private theorem frac_eq_trans : transitive frac_eq :=
begin
  intros x y z,
  assume hxy hyz,
  unfold frac_eq at hxy hyz,
  unfold frac_eq,
  have h := congr_arg (λ x : myint, x * z.denom) hxy,
  dsimp only [] at h,
  -- This is disgusting. We need to hide the mynat theorems behind
  -- their own namespace.
  rw [@myint.mul_assoc y.num, @myint.mul_comm x.denom,
      ←@myint.mul_assoc y.num, hyz] at h,
  suffices : y.denom * (x.num * z.denom) = y.denom * (z.num * x.denom),
    from myint.mul_cancel (lt_imp_ne y.denom_pos).symm this,
  rw [←myint.mul_assoc, @myint.mul_comm y.denom, h],
  ac_refl,
end

instance frac.setoid : setoid frac :=
⟨frac_eq, ⟨frac_eq_refl, frac_eq_symm, frac_eq_trans⟩⟩

theorem setoid_equiv (x y : frac) :
x ≈ y ↔ x.num * y.denom = y.num * x.denom := iff.rfl

theorem sound_exact_iff (x y: frac):
⟦x⟧ = ⟦y⟧ ↔ x ≈ y := iff.intro quotient.exact quotient.sound

instance decidable_frac_eq: ∀ a b: frac, decidable (a ≈ b) :=
begin
  intros a b,
  rw setoid_equiv,
  from myint.decidable_eq _ _,
end

end frac

end hidden
