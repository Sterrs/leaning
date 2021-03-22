import .basic

namespace hidden

open myring
open ordered_myring
open myfield
open ordered_myfield

namespace cau_seq

-- We have to prove that it actually gives a cau_seq
def add : cau_seq → cau_seq → cau_seq :=
λ f g, ⟨λ n, f.val n + g.val n,
begin
  have hf := f.property,
  have hg := g.property,
  dsimp only [is_cau_seq] at *,
  intros ε hε,
  have hfε := hf (ε / 2) (half_pos hε),
  have hgε := hg (ε / 2) (half_pos hε),
  clear hf hg,
  cases hfε with M hM,
  cases hgε with N hN,
  existsi mynat.max M N,
  intros m n hm hn,
  have : f.val n + g.val n - (f.val m + g.val m) = (f.val n - f.val m) + (g.val n - g.val m),
    rw [sub_def, neg_distr],
    have : f.val n + g.val n + (-f.val m + -g.val m) = (f.val n + -f.val m) + (g.val n + -g.val m),
      ac_refl,
    rw this, clear this,
    rw [←sub_def, ←sub_def],
  rw this, clear this,
  have : abs (f.val n - f.val m + (g.val n - g.val m)) ≤
         abs (f.val n - f.val m) + abs (g.val n - g.val m),
    apply triangle_ineq,
  apply le_lt_chain (abs (f.val n - f.val m) + abs (g.val n - g.val m)),
    assumption,
  have hN₁ := hN m n (mynat.max_lt_cancel_right hm) (mynat.max_lt_cancel_right hn),
  have hM₁ := hM m n (mynat.max_lt_cancel_left hm) (mynat.max_lt_cancel_left hn),
  clear this hM hN,
  have := lt_comb hM₁ hN₁,
  rw [div_def, ←mul_add, ←one_div, half_plus_half (myrat.two_nzero), mul_one] at this,
  assumption,
end⟩

instance: has_add cau_seq := ⟨add⟩

theorem add_val {a b : cau_seq} {n : mynat} : (a + b).val n = a.val n + b.val n := rfl

end cau_seq

namespace real

open cau_seq

def add : real → real → real :=
quotient.lift₂ (λ f g, ⟦f + g⟧)
begin
  intros a x b y hab hxy,
  dsimp only [],
  rw cau_seq.class_equiv,
  rw cau_seq.setoid_equiv at *,
  dsimp only [cau_seq.equivalent] at *,
  intros ε hε,
  cases hab (ε / 2) (half_pos hε) with M hM,
  cases hxy (ε / 2) (half_pos hε) with N hN,
  existsi mynat.max M N,
  intros n hn,
  have hMn := hM n (mynat.max_lt_cancel_left hn),
  have hNn := hN n (mynat.max_lt_cancel_right hn),
  clear hM hN hxy hab,
  have h := lt_comb hMn hNn,
  rw half_plus_half at h,
  rw [cau_seq.add_val, cau_seq.add_val, sub_def, neg_distr],
  have : a.val n + x.val n + (-b.val n + -y.val n) = a.val n + -b.val n + (x.val n + -y.val n),
    ac_refl,
  rw this, clear this,
  apply le_lt_chain (abs (a.val n - b.val n) + abs (x.val n - y.val n)),
    rw [sub_def, sub_def],
    from @triangle_ineq _ _ (a.val n + -b.val n) (x.val n + -y.val n),
    assumption,
  from myrat.two_nzero,
end

instance : has_add real := ⟨add⟩

theorem add_eq_cls {x y : real} {f g : cau_seq}: x = ⟦f⟧ → y = ⟦g⟧ → x + y = ⟦f + g⟧ :=
λ hxf hyg, by rw [hxf, hyg]; refl

private theorem add_assoc (x y z : real) : x + y + z = x + (y + z) :=
begin
  cases quotient.exists_rep x with f hf, subst hf,
  cases quotient.exists_rep y with g hg, subst hg,
  cases quotient.exists_rep z with h hh, subst hh,
  repeat { rw [add_eq_cls rfl rfl] },
  apply seq_eq_imp_real_eq rfl rfl,
  intro n,
  repeat { rw add_val, },
  ac_refl,
end

instance add_is_assoc : is_associative real add := ⟨add_assoc⟩

@[simp]
private theorem add_zero (x : real) : x + 0 = x :=
begin
  cases quotient.exists_rep x with f hf, subst hf,
  rw [real_zero, coe_def],
  rw add_eq_cls rfl rfl,
  apply seq_eq_imp_real_eq rfl rfl,
  intro n,
  rw add_val,
  dsimp only [],
  rw add_zero,
end

@[simp]
private theorem add_neg (x : real) : x + -x = 0 :=
begin
  cases quotient.exists_rep x with f hf, subst hf,
  rw [neg_eq_cls rfl, add_eq_cls rfl rfl],
  rw real_zero,
  apply seq_eq_imp_real_eq rfl rfl,
  intro n,
  dsimp only [],
  rw [add_val, neg_val, ←sub_def, sub_self],
end

theorem real_two : (2 : real) = ↑(2 : myrat) := sorry

theorem two_nzero : (2 : real) ≠ 0 :=
begin
  rw [real_two, real_zero],
  assume water,
  rw eq_iff_coe_eq at water,
  exact myrat.two_nzero water,
end

end real

end hidden
