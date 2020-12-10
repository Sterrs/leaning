import .basic

namespace hidden

namespace cau_seq

-- We have to prove that it actually gives a cau_seq
def add : cau_seq → cau_seq → cau_seq :=
λ f g, ⟨λ n, f.val n + g.val n,
begin
  have hf := f.property,
  have hg := g.property,
  dsimp only [is_cau_seq] at *,
  intros ε hε,
  have hfε := hf (ε / 2) (myrat.half_pos hε),
  have hgε := hg (ε / 2) (myrat.half_pos hε),
  clear hf hg,
  cases hfε with M hM,
  cases hgε with N hN,
  existsi mynat.max M N,
  intros m n hm hn,
  have : f.val n + g.val n - (f.val m + g.val m) = (f.val n - f.val m) + (g.val n - g.val m),
    rw [←myrat.sub_add_neg, myrat.neg_add],
    have : f.val n + g.val n + (-f.val m + -g.val m) = (f.val n + -f.val m) + (g.val n + -g.val m),
      ac_refl,
    rw this, clear this,
    rw [myrat.sub_add_neg, myrat.sub_add_neg],
  rw this, clear this,
  have : myrat.abs (f.val n - f.val m + (g.val n - g.val m)) ≤
         myrat.abs (f.val n - f.val m) + myrat.abs (g.val n - g.val m),
    apply myrat.triangle_ineq,
  apply myrat.le_lt_chain ((f.val n - f.val m).abs + (g.val n - g.val m).abs),
    assumption,
  have hN₁ := hN m n (mynat.max_lt_cancel_right hm) (mynat.max_lt_cancel_right hn),
  have hM₁ := hM m n (mynat.max_lt_cancel_left hm) (mynat.max_lt_cancel_left hn),
  clear this hM hN,
  have := myrat.lt_comb hM₁ hN₁,
  rw myrat.half_plus_half at this,
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
  cases hab (ε / 2) (myrat.half_pos hε) with M hM,
  cases hxy (ε / 2) (myrat.half_pos hε) with N hN,
  existsi mynat.max M N,
  intros n hn,
  have hMn := hM n (mynat.max_lt_cancel_left hn),
  have hNn := hN n (mynat.max_lt_cancel_right hn),
  clear hM hN hxy hab,
  have h := myrat.lt_comb hMn hNn,
  rw myrat.half_plus_half at h,
  rw [cau_seq.add_val, cau_seq.add_val, ←myrat.sub_add_neg, myrat.neg_add],
  have : a.val n + x.val n + (-b.val n + -y.val n) = a.val n + -b.val n + (x.val n + -y.val n),
    ac_refl,
  rw this, clear this,
  apply myrat.le_lt_chain (myrat.abs (a.val n - b.val n) + myrat.abs (x.val n - y.val n)),
    from myrat.triangle_ineq _ _,
  assumption,
end

instance : has_add real := ⟨add⟩

variables x y z w : real

def sub := x + -y

instance : has_sub real := ⟨sub⟩

theorem sub_add_neg : x - y = x + -y := rfl

theorem add_eq_cls {x y : real} {f g : cau_seq}: x = ⟦f⟧ → y = ⟦g⟧ → x + y = ⟦f + g⟧ :=
λ hxf hyg, by rw [hxf, hyg]; refl

theorem add_comm : x + y = y + x :=
begin
  cases quotient.exists_rep x with f hf, subst hf,
  cases quotient.exists_rep y with g hg, subst hg,
  repeat { rw [add_eq_cls rfl rfl] },
  apply seq_eq_imp_real_eq rfl rfl,
  intro n,
  rw [add_val, add_val, myrat.add_comm],
end

instance add_is_comm : is_commutative real add := ⟨add_comm⟩

theorem add_assoc : x + y + z = x + (y + z) :=
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
theorem add_zero : x + 0 = x :=
begin
  cases quotient.exists_rep x with f hf, subst hf,
  rw real_zero,
  rw add_eq_cls rfl rfl,
  apply seq_eq_imp_real_eq rfl rfl,
  intro n,
  rw add_val,
  dsimp only [],
  rw myrat.add_zero,
end

@[simp]
theorem zero_add : 0 + x = x :=
by rw [add_comm, add_zero]

@[simp]
theorem neg_add : -(x + y) = -x + -y :=
begin
  cases quotient.exists_rep x with f hf, subst hf,
  cases quotient.exists_rep y with g hg, subst hg,
  repeat { rw add_eq_cls rfl rfl <|> rw neg_eq_cls rfl, },
  apply seq_eq_imp_real_eq rfl rfl,
  intro n,
  repeat { rw neg_val <|> rw add_val, },
  rw myrat.neg_add,
end

@[simp]
theorem neg_self_add : -x + x = 0 :=
begin
  cases quotient.exists_rep x with f hf, subst hf,
  rw [neg_eq_cls rfl, add_eq_cls rfl rfl],
  rw real_zero,
  apply seq_eq_imp_real_eq rfl rfl,
  intro n,
  dsimp only [],
  rw [add_val, neg_val, myrat.neg_self_add],
end

@[simp]
theorem self_neg_add : x + -x = 0 :=
by rw [add_comm, neg_self_add]

@[simp]
theorem sub_self : x - x = 0 :=
by rw [sub_add_neg, self_neg_add]

theorem two_nzero : (2 : real) ≠ 0 := sorry

end real

end hidden
