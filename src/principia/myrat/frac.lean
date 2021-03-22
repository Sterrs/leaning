import ..myint.lt
import ..myint.max

namespace hidden

open myint
open myring
open ordered_myring
open ordered_integral_domain

structure frac :=
-- Numerator
(num : myint)
-- Denominator
(denom : myint)
-- Proof that the denominator is positive
(denom_pos : 0 < denom)

namespace frac

variables {x y z : frac}

theorem num_and_denom_eq : x = y ↔ x.num = y.num ∧ x.denom = y.denom :=
begin
  split; assume h, {
    split; rw h,
  }, {
    cases x,
    cases y,
    cc,
  },
end

def frac_eq (x y: frac): Prop :=
x.num * y.denom = y.num * x.denom

private theorem frac_eq_refl: reflexive frac_eq :=
begin
  intro x,
  unfold frac_eq,
end

private theorem frac_eq_symm: symmetric frac_eq :=
begin
  intros x y,
  assume h,
  from h.symm,
end

private theorem frac_eq_trans: transitive frac_eq :=
begin
  intros x y z,
  assume hxy hyz,
  unfold frac_eq at hxy hyz,
  unfold frac_eq,
  have h := congr_arg (λ x : myint, x * z.denom) hxy,
  dsimp only [] at h,
  rw [mul_assoc y.num, mul_comm x.denom, ←mul_assoc y.num, hyz] at h,
  suffices : y.denom * (x.num * z.denom) = y.denom * (z.num * x.denom),
    from integral_domain.mul_cancel_left _ _ _ (lt_impl_ne _ _ y.denom_pos).symm this,
  rw [←mul_assoc, mul_comm y.denom, h],
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

def neg (x : frac) : frac :=
⟨-x.num, x.denom, x.denom_pos⟩

instance: has_neg frac := ⟨neg⟩

theorem neg_num {x : frac} :
(-x).num = -x.num := rfl

theorem neg_denom {x : frac} :
(-x).denom = x.denom := rfl

theorem frac_neg_neg {x: frac}: -x = neg x := rfl

theorem neg_well_defined (x y : frac) :
x ≈ y → ⟦-x⟧ = ⟦-y⟧ :=
begin
  assume h,
  apply quotient.sound,
  rw setoid_equiv,
  repeat { rw neg_num <|> rw neg_denom <|> rw neg_mul },
  rw ←neg_eq,
  rwa ←setoid_equiv,
end

def add (x y: frac) : frac :=
⟨x.num * y.denom + y.num * x.denom, x.denom * y.denom,
by from zero_lt_mul _ _ x.denom_pos y.denom_pos⟩

instance: has_add frac := ⟨add⟩

theorem frac_add_add (x y: frac): add x y = x + y := rfl

theorem add_num {x y : frac} :
(x + y).num = x.num * y.denom + y.num * x.denom := rfl

theorem add_denom {x y : frac} :
(x + y).denom = x.denom * y.denom := rfl

theorem add_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → ⟦a + x⟧ = ⟦b + y⟧ :=
begin
  assume hab hxy,
  rw frac.setoid_equiv at hab hxy,
  apply quotient.sound,
  rw [setoid_equiv, add_num, add_num, add_denom, add_denom,
      add_mul, add_mul],
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

def mul (x y : frac) : frac :=
⟨x.num * y.num, x.denom * y.denom,
by from zero_lt_mul _ _ x.denom_pos y.denom_pos⟩

instance: has_mul frac := ⟨mul⟩

theorem mul_num {x y : frac} :
(x * y).num = x.num * y.num := rfl

theorem mul_denom {x y : frac} :
(x * y).denom = x.denom * y.denom := rfl

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

private lemma one_pos: (0: myint) < 1 := nontrivial_zero_lt_one myint.nontrivial

-- Reciprocal of zero is zero
-- This has to be an if, because 0 is a different case
def inv (x: frac): frac :=
if h : x.num = 0 then ⟨0, 1, one_pos⟩ else
⟨(sign x.num) * x.denom, (sign x.num) * x.num, 
  zero_lt_sign_mul_self _ h⟩

instance: has_inv frac := ⟨inv⟩

private theorem inv_ite {x : frac} : x⁻¹ = dite (x.num = 0) (λ (h : x.num = 0), ⟨0, 1, one_pos⟩)
    (λ (h : ¬x.num = 0),⟨(sign x.num) * x.denom, (sign x.num) * x.num, zero_lt_sign_mul_self _ h⟩)
:= rfl

theorem inv_zero {x : frac} (h : x.num = 0) : x⁻¹ = ⟨0, 1, one_pos⟩ :=
by rw [inv_ite, dif_pos h]

theorem inv_num_nonzero {x : frac} (h : x.num ≠ 0) :
x⁻¹.num = (sign x.num) * x.denom :=
by rw [inv_ite, dif_neg h]

theorem inv_denom_nonzero {x : frac} (h : x.num ≠ 0) :
x⁻¹.denom = (sign x.num) * x.num :=
by rw [inv_ite, dif_neg h]

theorem inv_well_defined (x y : frac) :
x ≈ y → ⟦x⁻¹⟧ = ⟦y⁻¹⟧ :=
begin
  assume hxy,
  rw setoid_equiv at hxy,
  apply quotient.sound,
  rw setoid_equiv,
  by_cases x.num = 0, {
    rw [h, zero_mul] at hxy,
    have hzero := integral_domain.mul_integral _ _ hxy.symm,
    cases hzero, {
      rw [inv_zero h, inv_zero hzero],
    }, {
      exfalso, from (lt_impl_ne _ _ x.denom_pos) hzero.symm,
    },
  }, {
    have hydn0 : y.denom ≠ 0,
      from (lt_impl_ne _ _ y.denom_pos).symm,
    have hlhsn0 : x.num * y.denom ≠ 0,
      assume hz,
      cases integral_domain.mul_integral _ _ hz; contradiction,
    have : y.num ≠ 0,
      rw hxy at hlhsn0,
      assume hy0,
      rw hy0 at hlhsn0,
      rw zero_mul at hlhsn0,
      contradiction,
    rw [inv_denom_nonzero h, inv_num_nonzero h],
    rw [inv_denom_nonzero this, inv_num_nonzero this],
    have h₁ : sign x.num * x.denom * (sign y.num * y.num) =
      sign x.num * sign y.num * (y.num * x.denom),
      ac_refl,
    rw [h₁, ←hxy],
    ac_refl,
  },
end

end frac

end hidden
