import .basic

namespace hidden

open myint

-- Define addition on frac, show it is well-defined w.r.t. myrat
namespace frac

def add (x y : frac) : frac :=
⟨x.num * y.denom + y.num * x.denom, x.denom * y.denom,
by from zero_lt_mul x.denom_pos y.denom_pos⟩

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

variables {x y z : frac}

theorem add_comm : x + y = y + x :=
begin
  rw num_and_denom_eq,
  repeat { rw add_num <|> rw add_denom },
  split; ac_refl,
end

theorem add_assoc : x + y + z = x + (y + z) :=
begin
  rw num_and_denom_eq,
  repeat { rw add_num <|> rw add_denom <|> rw myint.add_mul },
  split; ac_refl,
end

theorem neg_add: -(x + y) = (-x) + (-y) :=
begin
  rw num_and_denom_eq,
  split, {
    rw neg_num,
    rw add_num,
    rw add_num,
    rw neg_num,
    rw neg_num,
    rw neg_denom,
    rw neg_denom,
    rw myint.neg_distr,
    rw myint.neg_mul,
    rw myint.neg_mul,
  }, {
    rw neg_denom,
    rw add_denom,
    rw add_denom,
    rw neg_denom,
    rw neg_denom,
  },
end

theorem sub_self: x + -x = ⟨0, x.denom * x.denom, zero_lt_mul x.denom_pos x.denom_pos⟩ :=
begin
  rw num_and_denom_eq,
  split, {
    rw add_num,
    rw neg_num,
    rw neg_denom,
    rw myint.neg_mul,
    rw myint.self_neg_add,
  }, {
    rw add_denom,
    rw neg_denom,
  },
end

end frac

-- Define addition for myrat, prove things about it
namespace myrat

def add : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x + y⟧) frac.add_well_defined

instance: has_add myrat := ⟨add⟩

theorem add_eq_cls {x y: frac} {a b: myrat}:
a = ⟦x⟧ → b = ⟦y⟧ → a + b = ⟦x + y⟧ :=
λ hax hay, by rw [hax, hay]; refl

def sub (x y : myrat) : myrat :=
x + -y

instance: has_sub myrat := ⟨sub⟩

theorem sub_eq_cls {x y: frac} {a b: myrat}:
a = ⟦x⟧ → b = ⟦y⟧ → a - b = ⟦x + -y⟧ :=
λ hax hay, by rw [hax, hay]; refl

variables {x y z : myrat}
variables {m n k : myint}

theorem sub_add_neg: x + -y = x - y := rfl

theorem add_coe: (↑m : myrat) + ↑n = ↑(m + n) :=
begin
  repeat { rw coe_int, },
  rw [add_eq_cls rfl rfl, ←frac.frac_add_add],
  dsimp [frac.add],
  repeat {rw myint.mul_one},
  refl,
end

theorem neg_coe: -(↑m : myrat) = ↑(-m) :=
begin
  repeat { rw coe_int, },
  rw [neg_eq_cls rfl, frac.frac_neg_neg],
  dsimp [frac.neg],
  refl,
end

theorem add_zero: x + 0 = x :=
begin
  cases quotient.exists_rep x with a ha,
  rw [←ha, rat_zero, add_eq_cls rfl rfl, ←frac.frac_add_add],
  dsimp [frac.add],
  rw [myint.mul_one, myint.zero_mul, myint.add_zero],
  conv in (a.denom * 1) {
    rw myint.mul_one,
  },
  congr,
  rw frac.num_and_denom_eq,
  from and.intro rfl rfl,
end

theorem add_comm: x + y = y + x :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  rw [←ha, ←hb],
  repeat { rw add_eq_cls rfl rfl, },
  rw frac.add_comm,
end

@[simp]
theorem zero_add: 0 + x = x :=
begin
  rw add_comm,
  from add_zero,
end

instance add_is_comm: is_commutative myrat add := ⟨@add_comm⟩

theorem add_assoc: x + y + z = x + (y + z) :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  cases quotient.exists_rep z with c hc,
  rw [←ha, ←hb, ←hc],
  repeat { rw add_eq_cls rfl rfl },
  rw frac.add_assoc,
end

instance add_is_assoc: is_associative myrat add := ⟨@add_assoc⟩

@[simp]
theorem abs_neg: abs (-x) = abs x :=
begin
  cases quotient.exists_rep x with a ha,
  rw [←ha, neg_eq_cls rfl, abs_eq_cls rfl, abs_eq_cls rfl,
      frac.abs_neg, frac.neg_neg],
end

@[simp]
theorem neg_neg: -(-x) = x :=
begin
  cases quotient.exists_rep x with a ha,
  rw [←ha, neg_eq_cls rfl, neg_eq_cls rfl, frac.neg_neg],
end

@[simp]
theorem neg_add: -(x + y) = -x + -y :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  rw [←ha, ←hb],
  repeat { rw neg_eq_cls rfl <|> rw add_eq_cls rfl rfl, },
  rw frac.neg_add,
end

@[simp]
theorem sub_self: x - x = 0 :=
begin
  cases quotient.exists_rep x with a ha,
  rw ←ha,
  rw sub_eq_cls rfl rfl,
  rw frac.sub_self,
  apply quotient.sound,
  rw frac.setoid_equiv,
  simp,
  rw myint.zero_mul,
  rw myint.zero_mul,
end

@[simp]
theorem neg_self_add : -x + x = 0 :=
by rw [add_comm, sub_add_neg, sub_self]

theorem abs_sub_switch : abs (x - y) = abs (y - x) :=
begin
  sorry,
end

end myrat

end hidden
