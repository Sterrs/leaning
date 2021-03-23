import .cau_seq
import ..logic

namespace hidden

open myring
open ordered_myring
open myfield
open ordered_myfield

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
  rwa [sub_def, neg_neg, add_comm, ←sub_def, ←abs_neg, neg_sub],
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
  rwa [sub_def, neg_neg, add_comm, ←sub_def, ←abs_neg, neg_sub],
end

end cau_seq

def real := quotient cau_seq.real_setoid

namespace real

def coe_myrat (a : myrat) : real := ⟦⟨λ n, a, cau_seq.constant_cauchy a⟩⟧

instance : has_coe myrat real := ⟨coe_myrat⟩

theorem coe_def (a : myrat) : (↑a : real) = ⟦⟨λ n, a, cau_seq.constant_cauchy a⟩⟧ := rfl

instance : has_zero real := ⟨↑(0 : myrat)⟩

theorem real_zero : (0 : real) = ↑(0 : myrat) := rfl

instance : has_one real := ⟨↑(1 : myrat)⟩

theorem real_one : (1 : real) = ↑(1 : myrat) := rfl

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
  rw ←cau_seq.setoid_equiv,
  apply cau_seq.seq_eq_impl_cau_seq_equiv,
  assumption,
end

theorem coe_neg (a : myrat) : -↑a = (↑(-a) : real) :=
begin
  rw coe_def,
  rw coe_def,
  rw neg_eq_cls rfl,
  apply seq_eq_imp_real_eq rfl rfl,
  intros n,
  rw cau_seq.neg_val,
end

open classical

theorem eq_iff_coe_eq (a b : myrat) : (↑a : real) = ↑b ↔ a = b :=
begin
  rw [coe_def, coe_def, cau_seq.class_equiv],
  split; assume h, {
    unfold cau_seq.equivalent at h,
    rw ←sub_to_zero_iff_eq,
    rw ←abs_zero_iff_zero,
    apply ordered_myring.le_antisymm, {
      rw le_iff_lt_impl_lt,
      intros ε hε,
      cases h ε hε with N hN,
      apply hN N (@mynat.le_refl N),
    }, {
      exact abs_nonneg _,
    },
  }, {
    intros ε hε,
    existsi (0 : mynat),
    intros n hn,
    dsimp,
    rwa [h, sub_self, abs_zero],
  },
end

theorem nontrivial : (0 : real) ≠ 1 :=
begin
  rw [real_zero, real_one],
  assume hydroxide,
  rw eq_iff_coe_eq at hydroxide,
  exact myrat.nontrivial hydroxide,
end

end real

end hidden
