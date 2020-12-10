import .frac

namespace hidden

open myint

namespace frac

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
  rw ←neg_cancel,
  rwa ←setoid_equiv,
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
  rw zero_lt_abs _ y.denom_pos,
  rw zero_lt_abs _ x.denom_pos,
  repeat {rw ←abs_mul},
  rw hxeqy,
end

end frac

def myrat := quotient frac.frac.setoid

namespace myrat

instance: decidable_eq myrat := quotient.decidable_eq

def f: myrat → myrat :=
λ x, if x = x then x else x

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

theorem neg_eq_cls {x: frac} {a: myrat}:
a = ⟦x⟧ → -a = ⟦-x⟧ :=
λ hax, by rw hax; refl

def abs : myrat → myrat :=
quotient.lift (λ x : frac, ⟦frac.abs x⟧) frac.abs_well_defined

instance: has_zero myrat := ⟨⟦⟨0, 1, zero_lt_one⟩⟧⟩

theorem abs_eq_cls {x: frac} {a: myrat}:
a = ⟦x⟧ → abs a = ⟦frac.abs x⟧ :=
λ hax, by rw hax; refl

theorem rat_zero: (0: myrat) = ⟦⟨0, 1, zero_lt_one⟩⟧ := rfl

instance: has_one myrat := ⟨⟦⟨1, 1, zero_lt_one⟩⟧⟩

theorem rat_one: (1: myrat) = ⟦⟨1, 1, zero_lt_one⟩⟧ := rfl

instance: has_coe myint myrat := ⟨λ m, ⟦⟨m, 1, zero_lt_one⟩⟧⟩

theorem one_nzero : (1 : myrat) ≠ 0 :=
begin
  assume hydroxide,
  have := quotient.exact hydroxide,
  rw frac.setoid_equiv at this,
  cases quotient.exact this,
end

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

theorem abs_zero : abs 0 = (0 : myrat) := rfl

@[simp]
theorem abs_neg (x : myrat) : abs (-x) = abs x :=
begin
  cases quotient.exists_rep x with a ha,
  rw [←ha, neg_eq_cls rfl, abs_eq_cls rfl, abs_eq_cls rfl,
      frac.abs_neg, frac.neg_neg],
end

theorem abs_plusminus {x: myrat}: abs x = x ∨ abs x = -x :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  repeat {rw abs_eq_cls rfl},
  rw neg_eq_cls rfl,
  repeat {rw frac.sound_exact_iff <|> rw frac.setoid_equiv},
  repeat {rw frac.abs_num <|> rw frac.abs_denom},
  cases myint.abs_eq_plusminus (a.num * a.denom) with h h, {
    left,
    rw myint.abs_mul at h,
    have := myint.zero_lt_abs _ a.denom_pos,
    rw ←this at h,
    assumption,
  }, {
    right,
    rw myint.abs_mul at h,
    have := myint.zero_lt_abs _ a.denom_pos,
    rw ←this at h,
    rw frac.neg_denom,
    rw frac.neg_num,
    rw mul_neg_with,
    assumption,
  },
end

@[simp]
theorem neg_neg (x : myrat) : -(-x) = x :=
begin
  cases quotient.exists_rep x with a ha,
  rw [←ha, neg_eq_cls rfl, neg_eq_cls rfl, frac.neg_neg],
end

end myrat

end hidden
