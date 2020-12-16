import .frac

namespace hidden

open myint
open myring
open ordered_myring

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

def neg : myrat → myrat :=
quotient.lift (λ x, ⟦-x⟧) frac.neg_well_defined

instance: has_neg myrat := ⟨neg⟩

theorem neg_eq_cls {x: frac} {a: myrat}:
a = ⟦x⟧ → -a = ⟦-x⟧ :=
λ hax, by rw hax; refl

private lemma one_pos: (0: myint) < 1 := nontrivial_zero_lt_one myint.nontrivial

instance: has_zero myrat := ⟨⟦⟨0, 1, one_pos⟩⟧⟩

theorem rat_zero: (0: myrat) = ⟦⟨0, 1, one_pos⟩⟧ := rfl

instance: has_one myrat := ⟨⟦⟨1, 1, one_pos⟩⟧⟩

theorem rat_one: (1: myrat) = ⟦⟨1, 1, one_pos⟩⟧ := rfl

instance: has_coe myint myrat := ⟨λ m, ⟦⟨m, 1, one_pos⟩⟧⟩

theorem nontrivial: (1: myrat) ≠ 0 :=
begin
  assume hydroxide,
  have := quotient.exact hydroxide,
  rw frac.setoid_equiv at this,
  cases quotient.exact this,
end

theorem coe_int {m : myint} : (↑m : myrat) = ⟦⟨m, 1, one_pos⟩⟧ :=
rfl

theorem coe_cancel {m n : myint}:
(↑m : myrat) = ↑n ↔ m = n :=
begin
  split; assume h, {
    rw [coe_int, coe_int, class_equiv] at h,
    dsimp only [] at h,
    rwa [mul_one, mul_one] at h,
  }, {
    congr, assumption,
  },
end

def add : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x + y⟧) frac.add_well_defined

instance: has_add myrat := ⟨add⟩

theorem add_eq_cls {x y: frac} {a b: myrat}:
a = ⟦x⟧ → b = ⟦y⟧ → a + b = ⟦x + y⟧ :=
λ hax hay, by rw [hax, hay]; refl

theorem two_nzero: (2: myrat) ≠ 0 :=
begin
  assume water,
  have := quotient.exact water,
  rw frac.setoid_equiv at this,
  cases (quotient.exact this),
end

def sub (x y : myrat) : myrat :=
x + -y

instance: has_sub myrat := ⟨sub⟩

theorem sub_eq_cls {x y: frac} {a b: myrat}:
a = ⟦x⟧ → b = ⟦y⟧ → a - b = ⟦x + -y⟧ :=
λ hax hay, by rw [hax, hay]; refl

variables {x y z : myrat}
variables {m n k : myint}

theorem add_coe: (↑m : myrat) + ↑n = ↑(m + n) :=
begin
  repeat { rw coe_int, },
  rw [add_eq_cls rfl rfl, ←frac.frac_add_add],
  dsimp [frac.add],
  repeat {rw myint.mul_one},
  rw frac.sound_exact_iff,
  rw frac.setoid_equiv,
  dsimp only [],
  repeat {rw mul_one},
end

theorem neg_coe: -(↑m : myrat) = ↑(-m) :=
begin
  repeat { rw coe_int, },
  rw [neg_eq_cls rfl, frac.frac_neg_neg],
  dsimp [frac.neg],
  refl,
end

def mul : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x * y⟧) frac.mul_well_defined

instance: has_mul myrat := ⟨mul⟩

def inv : myrat → myrat :=
quotient.lift (λ x, ⟦x⁻¹⟧) frac.inv_well_defined

instance: has_inv myrat := ⟨inv⟩

def div : myrat → myrat → myrat := λ x y, x * y⁻¹

instance: has_div myrat := ⟨div⟩

theorem div_eq_mul_inv : x / y = x * y⁻¹ := rfl

-- Multiplication

theorem mul_eq_cls {x y : frac} {a b : myrat} :
a = ⟦x⟧ → b = ⟦y⟧ → a * b = ⟦x * y⟧ :=
λ hax hby, by rw [hax, hby]; refl

-- Reciprocal "inv"

theorem inv_eq_cls {a : myrat} {x : frac}: a = ⟦x⟧ → a⁻¹ = ⟦x⁻¹⟧ :=
λ h, by rw h; refl

@[simp]
theorem zero_inv : 0⁻¹ = (0 : myrat) :=
begin
  rw [rat_zero, @inv_eq_cls _ ⟨0, 1, one_pos⟩ rfl],
  rw [class_equiv, frac.inv_zero],
  refl,
end

theorem inv_self_mul : x ≠ 0 → x * x⁻¹ = 1 :=
begin
  cases quotient.exists_rep x with a ha, subst ha,
  assume hx,
  rw [inv_eq_cls rfl, mul_eq_cls rfl rfl, rat_one],
  rw class_equiv,
  dsimp only [],
  rw [frac.mul_num, frac.mul_denom],
  have : a.num ≠ 0,
    rw rat_zero at hx,
    have h : ¬⟦a⟧ = ⟦{num := 0, denom := 1, denom_pos := one_pos}⟧,
      from hx,
    clear hx,
    rw [class_equiv, mul_one, zero_mul] at h,
    assumption,
  rw [frac.inv_num_nonzero this, frac.inv_denom_nonzero this],
  ac_refl,
end

instance: myring myrat := ⟨
  λ x y z: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    cases quotient.exists_rep z with c hc, subst hc,
    repeat {rw add_eq_cls rfl rfl},
    apply congr rfl,
    rw frac.num_and_denom_eq,
    repeat { rw frac.add_num <|> rw frac.add_denom <|> rw myring.add_mul },
    split; ac_refl,
  end,
  λ x: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    rw [rat_zero, add_eq_cls rfl rfl],
    rw frac.sound_exact_iff,
    rw frac.setoid_equiv,
    rw frac.add_denom,
    rw frac.add_num,
    dsimp only [],
    rw myring.zero_mul,
    rw myring.add_zero,
    repeat {rw myring.mul_one},
  end,
  λ x: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    rw neg_eq_cls rfl,
    rw add_eq_cls rfl rfl,
    apply quotient.sound,
    rw frac.setoid_equiv,
    dsimp only [],
    repeat {rw myring.zero_mul},
    rw frac.add_num,
    rw mul_one,
    rw frac.neg_denom,
    rw frac.neg_num,
    rw neg_mul,
    from add_neg _,
  end,
  λ x y z: myrat,
  begin
    cases quotient.exists_rep x with a ha,
    cases quotient.exists_rep y with b hb,
    cases quotient.exists_rep z with c hc,
    rw [←ha, ←hb, ←hc],
    repeat { rw mul_eq_cls rfl rfl, },
    rw class_equiv,
    repeat { rw frac.mul_num <|> rw frac.mul_denom, },
    ac_refl,
  end,
  λ x y: myrat,
  begin
    cases quotient.exists_rep x with a ha,
    cases quotient.exists_rep y with b hb,
    rw [←ha, ←hb],
    repeat { rw mul_eq_cls rfl rfl, },
    rw class_equiv,
    repeat { rw frac.mul_num <|> rw frac.mul_denom, },
    ac_refl,
  end,
  λ x: myrat,
  begin
    cases quotient.exists_rep x with a ha,
    rw [←ha, rat_one],
    rw mul_eq_cls rfl rfl,
    rw class_equiv,
    rw [frac.mul_num, frac.mul_denom],
    dsimp only [],
    repeat {rw myring.mul_one},
  end,
  λ x y z: myrat,
  begin
    cases quotient.exists_rep x with a ha, subst ha,
    cases quotient.exists_rep y with b hb, subst hb,
    cases quotient.exists_rep z with c hc, subst hc,
    repeat { rw mul_eq_cls rfl rfl <|> rw add_eq_cls rfl rfl, },
    rw class_equiv,
    repeat { rw frac.mul_num <|> rw frac.mul_denom <|> rw frac.add_num <|> rw frac.add_denom, },
    -- ac_refl can't expand brackets
    repeat { rw myring.add_mul <|> rw myring.mul_add, },
    ac_refl,
  end⟩

end myrat

end hidden
