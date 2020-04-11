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

theorem add_num {x y : frac} :
(x + y).num = x.num * y.denom + y.num * x.denom := rfl

theorem add_denom {x y : frac} :
(x + y).denom = x.denom * y.denom := rfl

def mul (x y : frac) : frac :=
⟨x.num * y.num, x.denom * y.denom,
by from zero_lt_mul x.denom_pos y.denom_pos⟩

instance: has_mul frac := ⟨mul⟩

theorem mul_num {x y : frac} :
(x * y).num = x.num * y.num := rfl

theorem mul_denom {x y : frac} :
(x * y).denom = x.denom * y.denom := rfl

-- Reciprocal of zero is zero
def inv (x : frac) : frac :=
if h : x.num = 0 then ⟨0, 1, zero_lt_one⟩ else
⟨(sign x.num) * x.denom, (sign x.num) * x.num, zero_lt_sign_mul_self h⟩

-- TODO: inv_num & inv_denom

instance: has_inv frac := ⟨inv⟩

-- Dividing by zero gives you zero
def div (x y : frac) : frac :=
x * y⁻¹

instance: has_div frac := ⟨div⟩

-- Basic rules of arithmetic

variables {x y z : frac}

theorem add_assoc : x + y + z = x + (y + z) :=
begin
  sorry, -- Not sure how or whether to prove this
end

-- Setoid for rationals

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

theorem setoid_equiv :
x ≈ y ↔ x.num * y.denom = y.num * x.denom := by refl

-- Well-definedness w.r.t. setoid

theorem add_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → ⟦a + x⟧ = ⟦b + y⟧ :=
begin
  assume hab hxy,
  rw setoid_equiv at hab hxy,
  apply quotient.sound,
  rw [setoid_equiv, add_num, add_num, add_denom, add_denom,
      myint.add_mul, myint.add_mul],
  -- State what we want ac_refl to do, then do it and rewrite
  have h₁ : x.num * a.denom * (b.denom * y.denom) =
            x.num * y.denom * a.denom * b.denom,
    ac_refl,
  rw [h₁, hxy],
  have h₂ : a.num * x.denom * (b.denom * y.denom) =
            a.num * b.denom * x.denom * y.denom,
    ac_refl,
  rw [h₂, hab],
  ac_refl,
end

theorem mul_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → ⟦a * x⟧ = ⟦b * y⟧ :=
begin
  assume hab hxy,
  rw setoid_equiv at hab hxy,
  apply quotient.sound,
  rw [setoid_equiv, mul_num, mul_num, mul_denom, mul_denom],
  -- State what we want ac_refl to do, then do it and rewrite
  have h₁ : a.num * x.num * (b.denom * y.denom) =
            x.num * y.denom * a.num * b.denom,
    ac_refl,
  rw [h₁, hxy],
  have h₂ : b.num * y.num * (a.denom * x.denom) =
            b.num * a.denom * x.denom * y.num,
    ac_refl,
  rw [h₂, ←hab],
  ac_refl,
end

private lemma neq_iff_not_eq (m n : myint): m ≠ n ↔ ¬(m = n) :=
begin
  split; assume hneq heq, all_goals { contradiction },
end

theorem inv_well_defined (x y : frac) :
x ≈ y → ⟦x⁻¹⟧ = ⟦y⁻¹⟧ :=
begin
  assume h,
  rw setoid_equiv at h,
  apply quotient.sound,
  rw setoid_equiv,
  sorry,
end

end frac

end hidden
