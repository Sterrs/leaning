import .add

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
    from myrat.lt_imp_ne hufpos hufeq0.symm,
  -- hug0 is frying right now
  have hug0 : ug ≠ 0,
    assume hugeq0,
    from myrat.lt_imp_ne hugpos hugeq0.symm,
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

end cau_seq

namespace real

open cau_seq

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


end real

end hidden
