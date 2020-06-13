import .frac

namespace hidden

open myint

namespace frac

-- TODO: Move this to frac.lean
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

def neg (x : frac) : frac :=
⟨-x.num, x.denom, x.denom_pos⟩

instance: has_neg frac := ⟨neg⟩

theorem neg_num {x : frac} :
(-x).num = -x.num := rfl

theorem neg_denom {x : frac} :
(-x).denom = x.denom := rfl

theorem frac_neg_neg {x: frac}: -x = neg x := rfl

def abs (x : frac) : frac :=
⟨myint.abs x.num, x.denom, x.denom_pos⟩

theorem abs_num (x: frac): (abs x).num = (myint.abs x.num) := rfl

theorem abs_denom (x: frac): (abs x).denom = x.denom := rfl

theorem abs_neg (x: frac): abs x = abs (-x) :=
begin
  rw num_and_denom_eq,
  split, {
    rw abs_num,
    rw abs_num,
    rw neg_num,
    rw myint.abs_neg,
  }, {
    rw abs_denom,
    rw abs_denom,
    rw neg_denom,
  },
end

theorem neg_neg (x: frac): -(-x) = x :=
begin
  rw num_and_denom_eq,
  split, {
    rw neg_num,
    rw neg_num,
    rw myint.neg_neg,
  }, {
    rw neg_denom,
    rw neg_denom,
  },
end

theorem neg_well_defined (x y : frac) :
x ≈ y → ⟦-x⟧ = ⟦-y⟧ :=
begin
  assume h,
  apply quotient.sound,
  rw setoid_equiv,
  repeat { rw neg_num <|> rw neg_denom <|> rw myint.neg_mul },
  rwa [neg_cancel, ←setoid_equiv],
end

theorem abs_well_defined (x y : frac) :
x ≈ y → ⟦abs x⟧ = ⟦abs y⟧ :=
begin
  assume hxeqy,
  rw setoid_equiv at hxeqy,
  apply quotient.sound,
  rw setoid_equiv,
  rw abs_num,
  rw abs_num,
  rw abs_denom,
  rw abs_denom,
  rw zero_lt_abs y.denom_pos,
  rw zero_lt_abs x.denom_pos,
  rw nat_nat_mul,
  rw nat_nat_mul,
  rw abs_distr,
  rw abs_distr,
  rw hxeqy,
end

end frac

def myrat := quotient frac.frac.setoid

namespace myrat

private lemma class_setoid (x y : frac) :
⟦x⟧ = ⟦y⟧ ↔ x ≈ y := iff.intro quotient.exact quotient.sound

theorem class_equiv {x y : frac} :
⟦x⟧ = ⟦y⟧ ↔ x.num * y.denom = y.num * x.denom :=
begin
  split; assume h,
    rwa [←frac.setoid_equiv, ←class_setoid],
  rwa [class_setoid, frac.setoid_equiv],
end

theorem equal_imp_equiv {x y : frac} (h : x = y) :  ⟦x⟧ = ⟦y⟧ :=
by congr; assumption

def neg : myrat → myrat :=
quotient.lift (λ x, ⟦-x⟧) frac.neg_well_defined

instance: has_neg myrat := ⟨neg⟩

theorem neg_eq_cls (x: frac) (a: myrat):
a = ⟦x⟧ → -a = ⟦-x⟧ :=
begin
  assume hax,
  rw hax,
  refl,
end

def abs : myrat → myrat :=
quotient.lift (λ x : frac, ⟦frac.abs x⟧) frac.abs_well_defined

instance: has_zero myrat := ⟨⟦⟨0, 1, zero_lt_one⟩⟧⟩

theorem abs_eq_cls (x: frac) (a: myrat):
a = ⟦x⟧ → abs a = ⟦frac.abs x⟧ :=
begin
  assume hax,
  rw hax,
  refl,
end

theorem rat_zero: (0: myrat) = ⟦⟨0, 1, zero_lt_one⟩⟧ := rfl

instance: has_one myrat := ⟨⟦⟨1, 1, zero_lt_one⟩⟧⟩

instance: has_coe myint myrat := ⟨λ m, ⟦⟨m, 1, zero_lt_one⟩⟧⟩

theorem coe_int {m : myint} : (↑m : myrat) = ⟦⟨m, 1, zero_lt_one⟩⟧ :=
rfl

theorem coe_cancel {m n : myint}:
(↑m : myrat) = ↑n ↔ m = n :=
begin
  split; assume h, {
    rw [coe_int, coe_int, class_equiv] at h,
    dsimp only [] at h,
    rwa [myint.mul_one, myint.mul_one] at h,
  }, {
    congr, assumption,
  },
end

end myrat

end hidden
