import .basic

namespace hidden

open myint

-- Define addition on frac, show it is well-defined w.r.t. myrat
namespace frac

def add (x y : frac) : frac :=
⟨x.num * y.denom + y.num * x.denom, x.denom * y.denom,
by from zero_lt_mul x.denom_pos y.denom_pos⟩

instance: has_add frac := ⟨add⟩

def neg (x : frac) : frac :=
⟨-x.num, x.denom, x.denom_pos⟩

instance: has_neg frac := ⟨neg⟩

theorem add_num {x y : frac} :
(x + y).num = x.num * y.denom + y.num * x.denom := rfl

theorem add_denom {x y : frac} :
(x + y).denom = x.denom * y.denom := rfl

theorem neg_num {x : frac} :
(-x).num = -x.num := rfl

theorem neg_denom {x : frac} :
(-x).denom = x.denom := rfl

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

theorem neg_well_defined (x y : frac) :
x ≈ y → ⟦-x⟧ = ⟦-y⟧ :=
begin
  assume h,
  rw myrat.class_equiv,
  repeat { rw neg_num <|> rw neg_denom <|> rw myint.neg_mul },
  rwa [neg_cancel, ←setoid_equiv],
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

end frac

-- Define addition for myrat, prove things about it
namespace myrat

def add : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x + y⟧) frac.add_well_defined

instance: has_add myrat := ⟨add⟩

def neg : myrat → myrat :=
quotient.lift (λ x, ⟦-x⟧) frac.neg_well_defined

instance: has_neg myrat := ⟨neg⟩

variables {x y z : myrat}
variables {m n k : myint}

theorem add_coe: (↑m : myrat) + ↑n = ↑(m + n) :=
begin
  sorry,
end

theorem neg_coe: -(↑m : myrat) = ↑(-m) :=
begin
  rw [coe_int, coe_int],
  sorry,
end

theorem add_zero: x + 0 = x := sorry

theorem zero_add: 0 + x = x := sorry

theorem add_comm: x + y = y + x := sorry

instance add_is_comm: is_commutative myrat add := ⟨@add_comm⟩

theorem add_assoc: x + y + z = x + (y + z) := sorry

instance add_is_assoc: is_associative myrat add := ⟨@add_assoc⟩

end myrat

end hidden
