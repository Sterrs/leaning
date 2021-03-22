import .add

noncomputable theory

namespace hidden

open myring
open ordered_myring
open myfield
open ordered_myfield
open ordered_integral_domain

namespace cau_seq

-- The proof is very similar to the one we use for real series in analysis.
-- We bound the absolute values of each of the series above, and
-- use the ax - by = a(x - y) + y(a - b) trick, along with the
-- triangle inequality and some appropriately chosen eventual bounds
-- on |x - y| and |a - b|
def mul : cau_seq → cau_seq → cau_seq :=
λ f g, ⟨λ n, f.val n * g.val n,
begin
  have hf := f.property,
  have hg := g.property,
  dsimp only [is_cau_seq] at *,
  intros ε hε,
  -- Use the fact that f and g have bounded absolute value
  cases cau_seq.abs_bounded_above f with uf huf,
  cases huf with hufpos huf,
  cases cau_seq.abs_bounded_above g with ug hug,
  cases hug with hugpos hug,
  -- to create some "magical" bound on the difference between
  -- term m and n
  have hεfpos : 0 < (ε / 2) / ug,
    rw [div_def, ←zero_mul (0 : myrat)],
    apply @lt_mul_comb_nonneg _ _ (0 : myrat) _ 0 _ (by refl) (by refl),
      from half_pos hε,
    from pos_impl_inv_pos hugpos,
  have hεgpos : 0 < (ε / 2) / uf,
    rw [div_def, ←zero_mul (0 : myrat)],
    apply @lt_mul_comb_nonneg _ _ (0 : myrat) _ 0 _ (by refl) (by refl),
      from half_pos hε,
    from pos_impl_inv_pos hufpos,
  cases hf ((ε / 2) / ug) hεfpos with M hM,
  cases hg ((ε / 2) / uf) hεgpos with N hN,
  clear hεfpos hεgpos hf hg, -- Tidy a bit
  -- Obvious facts are obvious
  existsi mynat.max M N,
  intros m n hm hn,
  have hMm : M < m, from mynat.max_lt_cancel_left hm,
  have hMn : M < n, from mynat.max_lt_cancel_left hn,
  have hNm : N < m, from mynat.max_lt_cancel_right hm,
  have hNn : N < n, from mynat.max_lt_cancel_right hn,
  clear hm hn,
  -- Now we need to use the "trick"
  have : f.val n * g.val n - f.val m * g.val m =
         f.val n * (g.val n - g.val m) + g.val m * (f.val n - f.val m),
  {
    repeat { rw sub_def <|> rw mul_add <|> rw mul_neg },
    have : f.val n * g.val n + -(f.val n * g.val m) + (g.val m * f.val n + -(g.val m * f.val m)) =
           f.val n * g.val n + - (f.val m * g.val m) + (f.val n * g.val m + - (f.val n * g.val m)),
      ac_refl,
    rw this, clear this,
    rw [add_neg, add_zero],
  },
  rw this, clear this,
  -- And the triangle inequality
  have : abs (f.val n * (g.val n - g.val m) + g.val m * (f.val n - f.val m)) ≤
         abs (f.val n * (g.val n - g.val m)) + abs (g.val m * (f.val n - f.val m)),
    apply triangle_ineq,
  apply le_lt_chain (abs (f.val n * (g.val n - g.val m)) +
                           abs (g.val m * (f.val n - f.val m))),
    assumption,
  clear this,
  -- Abs distrib over mul
  rw [abs_mul, abs_mul],
  -- Apply given hypotheses, after lots of rearranging so lean gets it
  -- Needed for rearranging
  have huf0 : uf ≠ 0,
    assume hufeq0,
    from lt_impl_ne hufpos hufeq0.symm,
  -- hug0 is frying right now
  have hug0 : ug ≠ 0,
    assume hugeq0,
    from lt_impl_ne hugpos hugeq0.symm,
  -- We juggle a bit so we can simply apply lt_comb
  conv {
    to_rhs,
    rw ←half_plus_half myrat.two_nzero ε,
    congr,
      rw ←div_mul_cancel (ε / 2) uf huf0,
      rw mul_comm,
      skip,
    rw ←div_mul_cancel (ε / 2) ug hug0,
    rw mul_comm,
  },
  -- This meaty line converts one goal into 8! (fortunately not 40320)
  apply lt_comb; apply lt_mul_comb_nonneg,
  -- Fortunately we can kill half of them in one go
  any_goals { apply abs_nonneg, },
  -- And the others are things we worked out earlier
  {
    from huf n,
  }, {
    from hN m n hNm hNn,
  }, {
    from hug m,
  }, {
    from hM m n hMm hMn,
  },
end⟩

instance: has_mul cau_seq := ⟨mul⟩

theorem mul_val {a b : cau_seq} {n : mynat} : (a * b).val n = a.val n * b.val n := rfl

theorem mul_comm (a b : cau_seq) : a * b = b * a :=
begin
  apply cau_seq.seq_eq_impl_eq,
  intro n,
  rw [mul_val, mul_val, myring.mul_comm],
end

open classical

local attribute [instance] classical.prop_decidable

def inv: cau_seq → cau_seq :=
λ f : cau_seq, ⟨(λ n : mynat, if f ≈ (0 : cau_seq) then 0 else (f.val n)⁻¹),
begin
  unfold is_cau_seq,
  intros ε hε,
  by_cases (f ≈ (0 : cau_seq)),
    existsi (0 : mynat),
    intros m n hm hn,
    rwa [if_pos h, if_pos h, sub_def, zero_add, abs_neg, abs_zero],
  have hf := f.property,
  unfold is_cau_seq at hf,
  cases cau_seq.nzero_impl_abs_eventually_bounded_below f h with A hA,
  cases hA with N hN,
  have h0AAε : 0 < A * (A * ε), {
    rw ←mul_zero (0 : myrat),
    apply @lt_mul_comb_nonneg _ _ 0 A 0 (A*ε) (by refl) (by refl) hN.left,
    rw ←mul_zero (0 : myrat),
    apply @lt_mul_comb_nonneg _ _ 0 A 0 ε (by refl) (by refl) hN.left,
    assumption,
  },
  cases hf (A*(A*ε)) h0AAε with M hM,
  existsi (mynat.max M N),
  intros m n hm hn,
  rw [if_neg h, if_neg h],
  have hnpos : 0 < abs (f.val n), {
    transitivity A,
      from hN.left,
    apply hN.right n,
    from mynat.max_lt_cancel_right hn,
  },
  have hnzero: f.val n ≠ 0, {
    assume this,
    rw this at hnpos,
    rw abs_zero at hnpos,
    apply lt_nrefl (0 : myrat),
    assumption,
  },
  rw lt_mul_pos_left _ hnpos,
  rw [←abs_mul, sub_def, mul_add, mul_inv hnzero],
  have hmpos : 0 < abs (f.val m), {
    transitivity A,
      from hN.left,
    apply hN.right m,
    from mynat.max_lt_cancel_right hm,
  },
  have hmzero: f.val m ≠ 0, {
    assume this,
    rw this at hmpos,
    rw abs_zero at hmpos,
    apply lt_nrefl (0 : myrat),
    assumption,
  },
  rw [lt_mul_pos_left _ hmpos, ←abs_mul, mul_add, mul_one, ←mul_assoc,
      myring.mul_comm, neg_mul, ←mul_assoc, inv_mul hmzero, one_mul, ←sub_def],
  suffices: A * (A * ε) ≤ abs (f.val m) * ((abs (f.val n)) * ε),
    apply lt_le_chain _ (A * (A * ε)),
    apply hM,
      from mynat.max_lt_cancel_left hn,
      from mynat.max_lt_cancel_left hm,
    assumption,
  apply le_mul_comb_nonneg, {
    from lt_impl_le hN.left,
  }, {
    rw ←zero_mul (0 : myrat),
    apply le_mul_comb_nonneg,
    refl, refl,
    from lt_impl_le hN.left,
    from lt_impl_le hε,
  }, {
    have := hN.right m (mynat.max_lt_cancel_right hm),
    apply lt_impl_le,
    assumption,
  },
  apply le_mul_comb_nonneg, {
    from lt_impl_le hN.left,
  }, {
    from lt_impl_le hε,
  }, {
    have := hN.right n (mynat.max_lt_cancel_right hn),
    apply lt_impl_le,
    assumption,
  },
  refl,
end⟩

instance: has_inv cau_seq := ⟨inv⟩

-- Lemma to help rewrite definitional equalities
lemma inv_val (f : cau_seq) (n : mynat) :
(f⁻¹).val n = if f ≈ (0 : cau_seq) then 0 else (f.val n)⁻¹ :=
rfl

theorem inv_equiv_zero (a : cau_seq) (h : a ≈ 0) : a⁻¹ ≈ 0 :=
begin
  apply cau_seq.seq_eq_impl_cau_seq_equiv,
  intro n,
  rw [inv_val, if_pos],
  refl,
  assumption,
end

end cau_seq

namespace real

private theorem mul_equiv (a b x : cau_seq) (hab : a ≈ b) : a * x ≈ b * x :=
begin
  rw cau_seq.setoid_equiv at *,
  intros q hq,
  cases cau_seq.abs_bounded_above x with u hu,
  cases hu with hu h,
  have hqu : 0 < q * u⁻¹,
    apply zero_lt_mul,
      assumption,
    apply pos_impl_inv_pos,
    assumption,
  cases hab (q * u⁻¹) hqu with N hN,
  existsi N,
  intros n hn,
  rw [cau_seq.mul_val, cau_seq.mul_val, ←sub_mul, abs_mul,
     lt_mul_pos_right u⁻¹ (pos_impl_inv_pos hu)],
  apply le_lt_chain (abs (a.val n - b.val n)), {
    conv {
      to_rhs,
      rw ←mul_one (abs (a.val n - b.val n)),
    },
    rw mul_assoc,
    apply le_mul_comb_nonneg, {
      exact abs_nonneg _,
    }, {
      apply zero_le_mul,
        exact abs_nonneg _,
      apply lt_impl_le,
      apply pos_impl_inv_pos,
      assumption,
    }, {
      refl,
    }, {
      have this : u ≠ 0,
        assume hu0,
        apply lt_impl_ne hu,
        symmetry, assumption,
      rw ←mul_inv this,
      have huinv : 0 ≤ u⁻¹,
        apply lt_impl_le,
        apply pos_impl_inv_pos,
        assumption,
      apply le_mul_nonneg_right _ _ u⁻¹ huinv,
      apply lt_impl_le,
      exact h n,
    },
  }, {
    exact hN n hn,
  },
end

def mul : real → real → real :=
quotient.lift₂ (λ f g, ⟦f * g⟧)
begin
  intros a x b y hab hxy,
  dsimp only [],
  rw [cau_seq.class_equiv, ←cau_seq.setoid_equiv],
  apply @setoid.trans _ _ _ (b * x),
    apply mul_equiv a b x,
    assumption,
  rw [cau_seq.mul_comm b, cau_seq.mul_comm b],
  apply mul_equiv x y b,
  assumption,
end

instance: has_mul real := ⟨mul⟩

theorem mul_eq_cls {a b : cau_seq} {x y : real} :
x = ⟦a⟧ → y = ⟦b⟧ → x * y = ⟦a * b⟧ :=
λ hax hby, by rw [hax, hby]; refl

open classical

local attribute [instance] classical.prop_decidable

def inv: real → real :=
quotient.lift (λ f, ⟦f⁻¹⟧)
begin
  intros a b hab,
  have ha := a.property,
  have hb := b.property,
  dsimp only [],
  by_cases ha0: a ≈ (0 : cau_seq), {
    have: b ≈ (0 : cau_seq),
      apply @setoid.trans cau_seq _ b a 0,
        apply @setoid.symm cau_seq _ a b,
        assumption,
      assumption,
    rw [cau_seq.class_equiv, ←cau_seq.setoid_equiv],
    apply @setoid.trans cau_seq _ a⁻¹ 0 b⁻¹,
      apply cau_seq.inv_equiv_zero,
      assumption,
    apply @setoid.symm cau_seq _ _ _,
    apply cau_seq.inv_equiv_zero,
    assumption,
  }, {
    have hb0 : ¬b ≈ (0 : cau_seq),
      assume hb0,
      apply ha0,
      apply @setoid.trans cau_seq _ a b 0,
        assumption,
      assumption,
    cases cau_seq.nzero_impl_abs_eventually_bounded_below a ha0 with A hA,
    cases cau_seq.nzero_impl_abs_eventually_bounded_below b hb0 with B hB,
    cases hA with N₁ hN₁,
    cases hB with N₂ hN₂,
    rw cau_seq.class_equiv,
    rw cau_seq.setoid_equiv at hab,
    dsimp only [cau_seq.equivalent] at hab ⊢,
    intros ε hε,
    have h0ABε : 0 < A * (B * ε), {
      rw ←zero_mul (0 : myrat),
      apply @lt_mul_comb_nonneg _ _  (0 : myrat) _ 0 _ (by refl) (by refl) hN₁.left,
      rw ←zero_mul (0 : myrat),
      apply @lt_mul_comb_nonneg _ _ (0 : myrat) _ 0 _ (by refl) (by refl) hN₂.left hε,
    },
    cases hab (A * (B * ε)) h0ABε with N₃ hN₃,
    existsi mynat.max (mynat.max N₁ N₂) N₃,
    intros n hn,
    rw [cau_seq.inv_val, cau_seq.inv_val, if_neg ha0, if_neg hb0],
    have hanpos : 0 < abs (a.val n), {
      transitivity A,
        from hN₁.left,
      apply hN₁.right n,
      apply @mynat.max_lt_cancel_left _ N₂ _,
      apply @mynat.max_lt_cancel_left _ N₃ _,
      assumption,
    },
    have hbnpos : 0 < abs (b.val n), {
      transitivity B,
        from hN₂.left,
      apply hN₂.right n,
      apply @mynat.max_lt_cancel_right N₁ _ _,
      apply @mynat.max_lt_cancel_left _ N₃ _,
      assumption,
    },
    have hanzero : a.val n ≠ 0, {
      assume this,
      rw this at hanpos,
      rw abs_zero at hanpos,
      apply lt_nrefl (0 : myrat),
      assumption,
    },
    have hbnzero : b.val n ≠ 0, {
      assume this,
      rw this at hbnpos,
      rw abs_zero at hbnpos,
      apply lt_nrefl (0 : myrat),
      assumption,
    },
    -- A small amount of rearranging...
    rw [lt_mul_pos_left _ hanpos, ←abs_mul, sub_def, mul_add,
        mul_inv hanzero, lt_mul_pos_left _ hbnpos, ←abs_mul,
        mul_add, mul_one, mul_neg, mul_neg, add_comm,
        mul_comm (a.val n), ←mul_assoc, mul_inv hbnzero,
        one_mul, ←abs_neg, neg_distr, neg_neg, ←sub_def],
    apply lt_le_chain _ (A * (B * ε)) _, {
      apply hN₃ n,
      apply mynat.max_lt_cancel_right hn,
    }, {
      rw [←mul_assoc (abs (b.val n)), mul_comm (abs (b.val n)), mul_assoc (abs (a.val n))],
      apply le_mul_comb_nonneg, {
        from lt_impl_le hN₁.left,
      }, {
        rw ←zero_mul (0 : myrat),
        apply @le_mul_comb_nonneg _ _ (0 : myrat) _ _ _ (by refl) (by refl),
        from lt_impl_le hN₂.left,
        from lt_impl_le hε,
      }, {
        apply lt_impl_le,
        apply hN₁.right n,
        apply @mynat.max_lt_cancel_left _ N₂ _,
        apply @mynat.max_lt_cancel_left _ N₃ _,
        assumption,
      },
      apply le_mul_comb_nonneg, {
        from lt_impl_le hN₂.left,
      }, {
        from lt_impl_le hε,
      }, {
        apply lt_impl_le,
        apply hN₂.right n,
        apply @mynat.max_lt_cancel_right N₁ _ _,
        apply @mynat.max_lt_cancel_left _ N₃ _,
        assumption,
      },
      refl,
    },
  },
end

instance: has_inv real := ⟨inv⟩

theorem inv_eq_cls {a : cau_seq} {x : real} :
x = ⟦a⟧ → x⁻¹ = ⟦a⁻¹⟧ :=
λ hax, by rw hax; refl

variables x y z : real

-- Use a b c for corresponding sequences

private theorem mul_comm (x y : real): x * y = y * x :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  have hxy := mul_eq_cls ha.symm hb.symm,
  have hyx := mul_eq_cls hb.symm ha.symm,
  apply seq_eq_imp_real_eq hxy hyx,
  intro n,
  repeat { rw cau_seq.mul_val, },
  rw mul_comm,
end

private theorem mul_zero: x * 0 = 0 :=
begin
  cases quotient.exists_rep x with a ha,
  apply seq_eq_imp_real_eq (mul_eq_cls ha.symm real_zero) real_zero,
  intro n,
  rw cau_seq.mul_val,
  dsimp only [],
  rw mul_zero,
end

private theorem mul_one: x * 1 = x :=
begin
  cases quotient.exists_rep x with a ha,
  apply seq_eq_imp_real_eq (mul_eq_cls ha.symm real_one) ha.symm,
  intro n,
  rw cau_seq.mul_val,
  dsimp only [],
  rw mul_one,
end

private theorem mul_assoc: x * y * z = x * (y * z) :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  cases quotient.exists_rep z with c hc,
  have h₁: x * y * z = ⟦a * b * c⟧,
    rw mul_eq_cls, rw mul_eq_cls,
    repeat { symmetry, assumption, },
  have h₂: x * (y * z) = ⟦a * (b * c)⟧,
    rw mul_eq_cls,
    symmetry, assumption,
    rw mul_eq_cls,
    symmetry, assumption,
    symmetry, assumption,
  apply seq_eq_imp_real_eq h₁ h₂,
  intro n,
  repeat { rw cau_seq.mul_val, },
  rw mul_assoc,
end

private theorem mul_add: x * (y + z) = x * y + x * z :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  cases quotient.exists_rep z with c hc,
  have h₁: x * (y + z) = ⟦a * (b + c)⟧,
    rw mul_eq_cls,
    symmetry, assumption,
    rw add_eq_cls,
    symmetry, assumption,
    symmetry, assumption,
  have h₂: x * y + x * z = ⟦a * b + a * c⟧,
    rw add_eq_cls,
    rw mul_eq_cls,
    repeat { symmetry, assumption, },
    rw mul_eq_cls,
    repeat { symmetry, assumption, },
  apply seq_eq_imp_real_eq h₁ h₂,
  intro n,
  rw [cau_seq.add_val, cau_seq.mul_val, cau_seq.add_val, cau_seq.mul_val,
      cau_seq.mul_val, mul_add],
end

-- Reciprocal "inv"

-- Not sure what this was supposed to be, might be useful
-- theorem  : ¬x = 0 → x = ⟦a⟧ → x⁻¹ = sorry := sorry

@[simp]
theorem one_inv : 1⁻¹ = (1 : real) :=
begin
  rw real_one,
  have h : (1 : real)⁻¹ = ⟦1⁻¹⟧,
    apply inv_eq_cls real_one,
  apply seq_eq_imp_real_eq h real_one,
  intro n,
  dsimp only [],
  sorry,
end

@[simp]
theorem zero_inv : 0⁻¹ = (0 : real) :=
begin
  have h : (0 : real)⁻¹ = ⟦0⁻¹⟧,
    apply inv_eq_cls real_zero,
  apply seq_eq_imp_real_eq h real_zero,
  intro n,
  dsimp only [],
  rw [cau_seq.inv_val, if_pos],
  apply @setoid.refl _ _ _,
end

private theorem mul_inv : x ≠ 0 → x * x⁻¹ = 1 :=
begin
  sorry,
end

local attribute [instance] prop_decidable

instance: myring real := ⟨
  by apply_instance,
  real.add_assoc,
  real.add_zero,
  real.add_neg,
  mul_assoc,
  mul_comm,
  mul_one,
  mul_add,
⟩

instance : myfield real := {
  mul_inv := mul_inv,
  nontrivial := real.nontrivial,
}

end real

end hidden
