import .cau_seq

namespace hidden

namespace cau_seq

private lemma class_setoid (f g : cau_seq) :
⟦f⟧ = ⟦g⟧ ↔ f ≈ g := iff.intro quotient.exact quotient.sound

theorem class_equiv {f g : cau_seq} :
⟦f⟧ = ⟦g⟧ ↔ cau_seq.equivalent f g  :=
begin
  split; assume h,
    rwa [←cau_seq.setoid_equiv, ←class_setoid],
  rwa [class_setoid, cau_seq.setoid_equiv],
end

variables f g : cau_seq

theorem neg_is_cauchy : is_cau_seq $ λ n, -f.val n :=
begin
  have hf := f.property,
  dsimp only [is_cau_seq] at *,
  intro ε,
  assume hε,
  cases hf ε hε with N hN,
  existsi N,
  intros n m,
  assume hn hm,
  have h := hN n m hn hm,
  rwa [←myrat.sub_add_neg, myrat.neg_neg, myrat.add_comm,
      myrat.sub_add_neg, myrat.abs_sub_switch],
end

def neg : cau_seq → cau_seq :=
λ f, ⟨λ n, -f.val n, neg_is_cauchy f⟩

instance : has_neg cau_seq := ⟨neg⟩

def neg_val {n : mynat}: (-f).val n = - f.val n := rfl

theorem neg_well_defined : f ≈ g → ⟦-f⟧ = ⟦-g⟧ :=
begin
  assume hfg,
  rw setoid_equiv at hfg,
  rw class_equiv,
  dsimp only [equivalent] at *,
  intros ε hε,
  cases hfg ε hε with N hN,
  existsi N,
  intros n hn,
  have h := hN n hn,
  rw [neg_val, neg_val],
  rwa [←myrat.sub_add_neg, myrat.neg_neg, myrat.add_comm,
      myrat.sub_add_neg, myrat.abs_sub_switch],
end

end cau_seq

def real := quotient cau_seq.real_setoid

namespace real

instance : has_zero real := ⟨⟦⟨λ n, 0, cau_seq.constant_cauchy 0⟩⟧⟩

theorem real_zero : (0 : real) = ⟦⟨λ n, 0, cau_seq.constant_cauchy 0⟩⟧ := rfl

instance : has_one real := ⟨⟦⟨λ n, 1, cau_seq.constant_cauchy 1⟩⟧⟩

theorem real_one : (1 : real) = ⟦⟨λ n, 1, cau_seq.constant_cauchy 1⟩⟧ := rfl

instance : has_coe myrat real := ⟨λ q, ⟦⟨λ n, q, cau_seq.constant_cauchy q⟩⟧⟩

def neg : real → real := quotient.lift (λ f, ⟦-f⟧) cau_seq.neg_well_defined

instance : has_neg real := ⟨neg⟩

theorem neg_eq_cls {x : real} {f : cau_seq} : x = ⟦f⟧ → -x = ⟦-f⟧ :=
λ hxf, by rw hxf; refl

theorem neg_val (f : cau_seq) (n : mynat): (-f).val n = -f.val n := rfl

-- Use this to prove things which hold
-- "trivially because there is a myrat theorem showing the sequences are the same"
theorem seq_eq_imp_real_eq {x y : real} {f g : cau_seq}: x = ⟦f⟧ → y = ⟦g⟧ →
(∀ n, f.val n = g.val n) → x = y :=
begin
  assume hxf hyg,
  subst hxf, subst hyg,
  assume heq,
  rw cau_seq.class_equiv,
  dsimp only [cau_seq.equivalent],
  intros ε hε,
  existsi (0 : mynat),
  intros n hn,
  rwa [heq n, myrat.sub_self],
end

theorem neg_neg (x : real) : -(-x) = x :=
begin
  cases quotient.exists_rep x with f hf, subst hf,
  repeat { rw neg_eq_cls rfl, },
  apply seq_eq_imp_real_eq rfl rfl,
  intro n,
  rw [neg_val, neg_val, myrat.neg_neg],
end

end real

end hidden
