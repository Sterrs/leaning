import .frac

namespace hidden

open myint

namespace frac

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
x ≈ y ↔ x.num * y.denom = y.num * x.denom := by refl

end frac

def myrat := quotient frac.frac.setoid

namespace myrat

private lemma class_setoid (x y : frac) :
⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
begin
  split; assume h, {
    apply quotient.exact,
    assumption,
  }, {
    apply quotient.sound,
    assumption,
  },
end

theorem class_equiv {x y : frac} :
⟦x⟧ = ⟦y⟧ ↔ x.num * y.denom = y.num * x.denom :=
begin
  split; assume h,
    rwa [←frac.setoid_equiv, ←class_setoid],
  rwa [class_setoid, frac.setoid_equiv],
end

theorem equal_imp_equiv {x y : frac} (h : x = y) :  ⟦x⟧ = ⟦y⟧ :=
by congr; assumption

instance: has_zero myrat := ⟨⟦⟨0, 1, zero_lt_one⟩⟧⟩

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
