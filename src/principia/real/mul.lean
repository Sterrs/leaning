import .add

noncomputable theory

namespace hidden

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
    rw [myrat.div_eq_mul_inv, ←@myrat.zero_mul 0],
    apply myrat.lt_mul_comb_nonneg (by refl) (by refl),
      from myrat.half_pos hε,
    rwa ←myrat.pos_iff_inv_pos,
  have hεgpos : 0 < (ε / 2) / uf,
    rw [myrat.div_eq_mul_inv, ←@myrat.zero_mul 0],
    apply myrat.lt_mul_comb_nonneg (by refl) (by refl),
      from myrat.half_pos hε,
    rwa ←myrat.pos_iff_inv_pos,
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
    repeat { rw ←myrat.sub_add_neg <|> rw myrat.mul_add <|> rw myrat.mul_with_neg },
    have : f.val n * g.val n + -(f.val n * g.val m) + (g.val m * f.val n + -(g.val m * f.val m)) =
           f.val n * g.val n + - (f.val m * g.val m) + (f.val n * g.val m + - (f.val n * g.val m)),
      ac_refl,
    rw this, clear this,
    rw [myrat.self_neg_add, myrat.add_zero],
  },
  rw this, clear this,
  -- And the triangle inequality
  have : (f.val n * (g.val n - g.val m) + g.val m * (f.val n - f.val m)).abs ≤
         (f.val n * (g.val n - g.val m)).abs + (g.val m * (f.val n - f.val m)).abs,
    apply myrat.triangle_ineq,
  apply myrat.le_lt_chain ((f.val n * (g.val n - g.val m)).abs +
                           (g.val m * (f.val n - f.val m)).abs),
    assumption,
  clear this,
  -- Abs distrib over mul
  rw [myrat.abs_mul, myrat.abs_mul],
  -- Apply given hypotheses, after lots of rearranging so lean gets it
  -- Needed for rearranging
  have huf0 : uf ≠ 0,
    assume hufeq0,
    from myrat.lt_impl_ne hufpos hufeq0.symm,
  -- hug0 is frying right now
  have hug0 : ug ≠ 0,
    assume hugeq0,
    from myrat.lt_impl_ne hugpos hugeq0.symm,
  -- We juggle a bit so we can simply apply lt_comb
  conv {
    to_rhs,
    rw ←@myrat.half_plus_half ε,
    congr,
      rw ←@myrat.div_mul_cancel (ε / 2) uf huf0,
      rw myrat.mul_comm,
      skip,
    rw ←@myrat.div_mul_cancel (ε / 2) ug hug0,
    rw myrat.mul_comm,
  },
  -- This meaty line converts one goal into 8! (fortunately not 40320)
  apply myrat.lt_comb; apply myrat.lt_mul_comb_nonneg,
  -- Fortunately we can kill half of them in one go
  any_goals { apply myrat.abs_nonneg, },
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
    rwa [if_pos h, if_pos h, ←myrat.sub_add_neg, myrat.zero_add, myrat.abs_neg, myrat.abs_zero],
  have hf := f.property,
  unfold is_cau_seq at hf,
  cases cau_seq.nzero_impl_abs_eventually_bounded_below f h with A hA,
  cases hA with N hN,
  have h0AAε : 0 < A * (A * ε), {
    repeat {
      rw ←@myrat.mul_zero 0,
      apply myrat.lt_mul_comb_nonneg (by refl) (by refl) hN.left,
    },
    assumption,
  },
  cases hf (A*(A*ε)) h0AAε with M hM,
  existsi (mynat.max M N),
  intros m n hm hn,
  rw [if_neg h, if_neg h],
  have hnpos : 0 < (f.val n).abs, {
    transitivity A,
      from hN.left,
    apply hN.right n,
    from mynat.max_lt_cancel_right hn,
  },
  have hnzero: f.val n ≠ 0, {
    assume this,
    rw this at hnpos,
    rw myrat.abs_zero at hnpos,
    apply myrat.lt_nrefl 0,
    assumption,
  },
  rw myrat.lt_mul_pos_left hnpos,
  rw [←myrat.abs_mul, ←myrat.sub_add_neg, myrat.mul_add, myrat.self_inv_mul hnzero],
  have hmpos : 0 < (f.val m).abs, {
    transitivity A,
      from hN.left,
    apply hN.right m,
    from mynat.max_lt_cancel_right hm,
  },
  have hmzero: f.val m ≠ 0, {
    assume this,
    rw this at hmpos,
    rw myrat.abs_zero at hmpos,
    apply myrat.lt_nrefl 0,
    assumption,
  },
  rw [myrat.lt_mul_pos_left hmpos, ←myrat.abs_mul, myrat.mul_add, myrat.mul_one, ←myrat.mul_assoc,
      myrat.mul_comm, myrat.mul_neg_with, ←myrat.mul_assoc, myrat.inv_self_mul hmzero, myrat.one_mul,
      myrat.sub_add_neg],
  suffices: A * (A * ε) ≤ (f.val m).abs * ((f.val n).abs * ε),
    apply myrat.lt_le_chain (A * (A * ε)),
    apply hM,
      from mynat.max_lt_cancel_left hn,
      from mynat.max_lt_cancel_left hm,
    assumption,
  apply myrat.le_mul_comb_nonneg, {
    from myrat.lt_impl_le 0 A hN.left,
  }, {
    rw ←@myrat.zero_mul 0,
    apply myrat.le_mul_comb_nonneg,
    refl, refl,
    from myrat.lt_impl_le 0 A hN.left,
    from myrat.lt_impl_le 0 ε hε,
  }, {
    have := hN.right m (mynat.max_lt_cancel_right hm),
    apply myrat.lt_impl_le _ _,
    assumption,
  },
  apply myrat.le_mul_comb_nonneg, {
    from myrat.lt_impl_le 0 A hN.left,
  }, {
    from myrat.lt_impl_le 0 ε hε,
  }, {
    have := hN.right n (mynat.max_lt_cancel_right hn),
    apply myrat.lt_impl_le _ _,
    assumption,
  },
  refl,
end⟩

instance: has_inv cau_seq := ⟨inv⟩

-- Lemma to help rewrite definitional equalities
lemma inv_def (f : cau_seq) (n : mynat) :
(f⁻¹).val n = if f ≈ (0 : cau_seq) then 0 else (f.val n)⁻¹ :=
rfl

theorem inv_equiv_zero (a : cau_seq) (h : a ≈ 0) : a⁻¹ ≈ 0 :=
begin
  apply cau_seq.seq_eq_impl_cau_seq_equiv,
  intro n,
  rw [inv_def, if_pos],
  refl,
  assumption,
end

end cau_seq

namespace real

def mul : real → real → real :=
quotient.lift₂ (λ f g, ⟦f * g⟧)
begin
  intros a x b y hab hxy,
  dsimp only [],
  rw cau_seq.class_equiv,
  rw cau_seq.setoid_equiv at *,
  dsimp only [cau_seq.equivalent] at *,
  intros ε hε,
  -- Proof basically identical to the above...?
  sorry,
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
      rw ←@myrat.zero_mul 0,
      apply myrat.lt_mul_comb_nonneg (by refl) (by refl) hN₁.left,
      rw ←@myrat.zero_mul 0,
      apply myrat.lt_mul_comb_nonneg (by refl) (by refl) hN₂.left hε,
    },
    cases hab (A * (B * ε)) h0ABε with N₃ hN₃,
    existsi mynat.max (mynat.max N₁ N₂) N₃,
    intros n hn,
    rw [cau_seq.inv_def, cau_seq.inv_def, if_neg ha0, if_neg hb0],
    have hanpos : 0 < (a.val n).abs, {
      transitivity A,
        from hN₁.left,
      apply hN₁.right n,
      apply @mynat.max_lt_cancel_left _ N₂ _,
      apply @mynat.max_lt_cancel_left _ N₃ _,
      assumption,
    },
    have hbnpos : 0 < (b.val n).abs, {
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
      rw myrat.abs_zero at hanpos,
      apply myrat.lt_nrefl 0,
      assumption,
    },
    have hbnzero : b.val n ≠ 0, {
      assume this,
      rw this at hbnpos,
      rw myrat.abs_zero at hbnpos,
      apply myrat.lt_nrefl 0,
      assumption,
    },
    -- A small amount of rearranging...
    rw [myrat.lt_mul_pos_left hanpos, ←myrat.abs_mul, ←myrat.sub_add_neg, myrat.mul_add,
        myrat.self_inv_mul hanzero, myrat.lt_mul_pos_left hbnpos, ←myrat.abs_mul,
        myrat.mul_add, myrat.mul_one, myrat.mul_with_neg, myrat.mul_with_neg, myrat.add_comm,
        myrat.mul_comm (a.val n), ←myrat.mul_assoc, myrat.self_inv_mul hbnzero,
        myrat.one_mul, ←myrat.abs_neg, myrat.neg_add, myrat.neg_neg, myrat.sub_add_neg],
    apply myrat.lt_le_chain (A * (B * ε)), {
      apply hN₃ n,
      apply mynat.max_lt_cancel_right hn,
    }, {
      rw [←@myrat.mul_assoc (b.val n).abs, myrat.mul_comm (b.val n).abs, @myrat.mul_assoc (a.val n).abs],
      apply myrat.le_mul_comb_nonneg, {
        from myrat.lt_impl_le _ _ hN₁.left,
      }, {
        rw ←@myrat.zero_mul 0,
        apply myrat.le_mul_comb_nonneg (by refl) (by refl),
        from myrat.lt_impl_le _ _ hN₂.left,
        from myrat.lt_impl_le _ _ hε,
      }, {
        apply myrat.lt_impl_le _ _,
        apply hN₁.right n,
        apply @mynat.max_lt_cancel_left _ N₂ _,
        apply @mynat.max_lt_cancel_left _ N₃ _,
        assumption,
      },
      apply myrat.le_mul_comb_nonneg, {
        from myrat.lt_impl_le _ _ hN₂.left,
      }, {
        from myrat.lt_impl_le _ _ hε,
      }, {
        apply myrat.lt_impl_le _ _,
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

def div: real → real → real :=
λ x y, x * y⁻¹

instance: has_div real := ⟨div⟩

variables x y z : real

-- Use a b c for corresponding sequences

theorem mul_comm (x y : real): x * y = y * x :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  have hxy := mul_eq_cls ha.symm hb.symm,
  have hyx := mul_eq_cls hb.symm ha.symm,
  apply seq_eq_imp_real_eq hxy hyx,
  intro n,
  repeat { rw cau_seq.mul_val, },
  rw myrat.mul_comm,
end

instance mul_is_comm: is_commutative real mul := ⟨@mul_comm⟩

theorem mul_zero: x * 0 = 0 :=
begin
  cases quotient.exists_rep x with a ha,
  apply seq_eq_imp_real_eq (mul_eq_cls ha.symm real_zero) real_zero,
  intro n,
  rw cau_seq.mul_val,
  dsimp only [],
  rw myrat.mul_zero,
end

theorem zero_mul: 0 * x = 0 :=
by rw [mul_comm, mul_zero]; refl

theorem mul_one: x * 1 = x :=
begin
  cases quotient.exists_rep x with a ha,
  apply seq_eq_imp_real_eq (mul_eq_cls ha.symm real_one) ha.symm,
  intro n,
  rw cau_seq.mul_val,
  dsimp only [],
  rw myrat.mul_one,
end

theorem one_mul: 1 * x = x :=
by rw [mul_comm, mul_one]; refl

theorem mul_assoc: x * y * z = x * (y * z) :=
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
  from myrat.mul_assoc,
end

instance mul_is_assoc: is_associative real mul := ⟨@mul_assoc⟩

theorem mul_add: x * (y + z) = x * y + x * z :=
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
  rw [cau_seq.add_val, cau_seq.mul_val, cau_seq.add_val, cau_seq.mul_val],
  from myrat.mul_add,
end

theorem add_mul: (x + y) * z = x * z + y * z :=
by rw [mul_comm, mul_add, mul_comm, mul_comm z]

theorem mul_with_neg : x * (-y) = -(x * y) :=
begin
  cases quotient.exists_rep x with a ha,
  cases quotient.exists_rep y with b hb,
  have h₁: x * -y = ⟦a * -b⟧,
    rw mul_eq_cls,
    symmetry, assumption,
    rw neg_eq_cls,
    symmetry, assumption,
  have h₂: -(x * y) = ⟦-(a * b)⟧,
    rw neg_eq_cls,
    rw mul_eq_cls,
    symmetry, assumption,
    symmetry, assumption,
  apply seq_eq_imp_real_eq h₁ h₂,
  intro n,
  rw [cau_seq.mul_val, cau_seq.neg_val, cau_seq.neg_val, cau_seq.mul_val],
  from myrat.mul_with_neg,
end

theorem mul_neg_with : (-x) * y = -(x * y) :=
by rw [mul_comm, mul_with_neg, mul_comm]

theorem mul_neg_neg: -x * -y = x * y :=
by rw [mul_with_neg, mul_neg_with, neg_neg]

-- Reciprocal "inv"

@[simp]
theorem one_inv : 1⁻¹ = (1 : real) :=
begin
  sorry,
end

@[simp]
theorem zero_inv : 0⁻¹ = (0 : real) :=
begin
  sorry,
end

@[simp]
theorem inv_inv : x⁻¹⁻¹ = x :=
begin
  sorry,
end

theorem inv_distr : (x * y)⁻¹ = x⁻¹ * y⁻¹ :=
begin
  sorry,
end

theorem inv_self_mul {x : real}: x ≠ 0 → x⁻¹ * x = 1 :=
begin
  sorry,
end

theorem self_inv_mul {x : real}: x ≠ 0 → x * x⁻¹ = 1 :=
begin
  sorry,
end

-- Division

theorem div_eq_mul_inv : x / y = x * y⁻¹ := rfl

@[simp]
theorem div_one : x / 1 = x :=
by rw [div_eq_mul_inv, one_inv, mul_one]

theorem one_div : 1 / x = x⁻¹ :=
by rw [div_eq_mul_inv, one_mul]

@[simp]
theorem zero_div : 0 / x = 0 :=
by rw [div_eq_mul_inv, zero_mul]

@[simp]
theorem div_zero : x / 0 = 0 :=
by rw [div_eq_mul_inv, zero_inv, mul_zero]

theorem mul_div_cancel {y : real}: y ≠ 0 → (x * y) / y = x :=
λ h, by rw [div_eq_mul_inv, mul_assoc, self_inv_mul h, mul_one]

theorem div_mul_cancel {y : real} : y ≠ 0 → (x / y) * y = x :=
λ h, by rw [div_eq_mul_inv, mul_assoc, inv_self_mul h, mul_one]

theorem self_div {x : real} : x ≠ 0 → x / x = 1 :=
λ h, by rw [div_eq_mul_inv, self_inv_mul h]

theorem div_inv_switch : x / y = (y / x)⁻¹ :=
by rw [div_eq_mul_inv, div_eq_mul_inv, inv_distr, inv_inv, mul_comm]

theorem add_div : (x + y) / z = x / z + y / z :=
by repeat { rw div_eq_mul_inv, }; rw add_mul

theorem one_plus_one : 1 + 1 = (2 : real):= rfl

theorem double_eq_add_self : 2 * x = x + x :=
by rw [←one_plus_one, add_mul, one_mul]

theorem half_plus_half {ε : real} : ε / 2 + ε / 2 = ε :=
begin
  rw [←double_eq_add_self, mul_comm, div_mul_cancel _ two_nzero],
end

-- theorem abs_mul : abs (x * y) = abs x * abs y :=
-- begin
--   sorry,
-- end

theorem mul_integral: x * y = 0 → x = 0 ∨ y = 0 :=
begin
  sorry,
end

end real

end hidden
