import ..myint.lt

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

-- Operations

def add (x y : frac) : frac :=
⟨x.num * y.denom + y.num * x.denom, x.denom * y.denom,
by from zero_lt_mul x.denom_pos y.denom_pos⟩

instance: has_add frac := ⟨add⟩

def mul (x y : frac) : frac :=
⟨x.num * y.num, x.denom * y.denom,
by from zero_lt_mul x.denom_pos y.denom_pos⟩

instance: has_mul frac := ⟨mul⟩

-- Reciprocal of zero is zero
def inv (x : frac) : frac :=
if h : x.num = 0 then ⟨0, 1, zero_lt_one⟩ else
⟨(sign x.num) * x.denom, (sign x.num) * x.num, zero_lt_sign_mul_self h⟩

instance: has_inv frac := ⟨inv⟩

-- Setoid for rationals

def frac_eq (x : frac) (y : frac):
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

-- Well-definedness w.r.t. setoid

theorem add_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → ⟦a + x⟧ = ⟦b + y⟧ :=
begin
  assume hab hxy,
  sorry,
end

theorem mul_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → ⟦a * x⟧ = ⟦b * y⟧ :=
begin
  assume hab hxy,
  sorry,
end

private lemma neq_iff_not_eq (m n : myint): m ≠ n ↔ ¬(m = n) :=
begin
  split; assume hneq heq, all_goals { contradiction },
end

theorem inv_well_defined (x y : frac) :
x ≈ y → ⟦x⁻¹⟧ = ⟦y⁻¹⟧ :=
begin
  assume h,
  suffices : x⁻¹ ≈ y⁻¹,
    apply quotient.sound,
    assumption,
  sorry,
end

-- Dividing by zero gives you zero
def div (x y : frac) : frac :=
x * y⁻¹

instance: has_div frac := ⟨div⟩

end frac

end hidden
