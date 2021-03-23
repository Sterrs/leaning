import .mul

noncomputable theory

namespace hidden

open myring
open ordered_myring
open integral_domain
open ordered_integral_domain
open myfield
open ordered_myfield

namespace cau_seq

def positive : cau_seq → Prop :=
λ f : cau_seq, ∃ ε : myrat,
0 < ε ∧ (∃ N : mynat, ∀ n, N ≤ n → ε < f.val n)

def positive_well_defined (f g : cau_seq) : f ≈ g → positive f = positive g :=
begin
    assume hequiv,
    apply propext,
    rw setoid_equiv at hequiv,
    dsimp [equivalent] at hequiv,
    dsimp [positive] at *,
    split; assume h,
    all_goals {
      cases h with ε h,
      cases h with hε h,
      cases h with N hN,
      have hhalf_ε₁ := hequiv (ε / 2),
      have hhalf_ε := hhalf_ε₁ (half_pos hε),
      clear hhalf_ε₁,
      cases hhalf_ε with M hM,
      existsi (ε / 2),
      split,
        from half_pos hε,
      existsi (mynat.max M N),
      intro n,
      assume hmax,
      have hf := hN n (mynat.max_le_cancel_right hmax),
      have hfg := hM n (mynat.max_le_cancel_left hmax),
      clear hmax hM hN M N hequiv,
      rw [lt_add_cancel_left (ε/2), half_plus_half myrat.two_nzero],
    },
    {
      have := abs_lt_right _ _ hfg,
      rw lt_add_cancel_right _ _ (g.val n) at this,
      rw sub_def at this,
      rw add_assoc at this,
      rw neg_add at this,
      rw add_zero at this,
      transitivity (f.val n); assumption,
    }, {
      have := abs_lt_left _ _ hfg,
      rw lt_add_cancel_right _ _ (-f.val n) at this,
      rw sub_def at this,
      rw add_comm (f.val n + _) at this,
      rw ←add_assoc at this,
      rw neg_add at this,
      rw zero_add at this,
      rw lt_neg_switch_iff at this,
      rw [neg_distr, neg_neg, neg_neg, neg_neg] at this,
      transitivity (g.val n); assumption,
    },
end

theorem zero_npos : ¬positive 0 :=
begin
  assume h,
  cases h with ε hε,
  cases hε with hε hN,
  cases hN with N hN,
  suffices : (0 : myrat) < 0,
    from lt_nrefl 0 this,
  transitivity ε,
    assumption,
  have h₁ := hN N mynat.le_refl,
  assumption,
end

end cau_seq

namespace real

def positive : real → Prop :=
quotient.lift cau_seq.positive cau_seq.positive_well_defined

private theorem pos_cls {x : real} {f : cau_seq} :
x = ⟦f⟧ → (positive x ↔ ∃ ε : myrat, 0 < ε ∧ (∃ N : mynat, ∀ n, N ≤ n → ε < f.val n)) :=
begin
  assume hxf,
  subst hxf,
  refl,
end

-- Because it's annoying to reorder manually
universe u
private lemma exists_rep {α : Sort u} [s : setoid α] (q : quotient s) : ∃ a : α, q = ⟦a⟧ :=
begin
  cases quotient.exists_rep q with a ha,
  existsi a,
  symmetry,
  assumption,
end

private theorem pos_add_closed (x y : real) : positive x → positive y → positive (x + y) :=
begin
  assume hx hy,
  cases exists_rep x with a ha,
  cases exists_rep y with b hb,
  subst ha, subst hb,
  change positive ⟦a + b⟧,
  rw pos_cls rfl,
  rw pos_cls rfl at hx,
  rw pos_cls rfl at hy,
  cases hx with ε hx,
  cases hx with hε hx,
  cases hx with N hN,
  cases hy with δ hy,
  cases hy with hδ hy,
  cases hy with M hM,
  existsi ε + δ,
  split, {
    rw ←zero_add (0 : myrat),
    apply lt_comb; assumption,
  }, {
    existsi mynat.max M N,
    intros n hn,
    rw cau_seq.add_val,
    apply lt_comb,
      exact hN n (mynat.max_le_cancel_right hn),
    exact hM n (mynat.max_le_cancel_left hn),
  },
end

private theorem pos_mul_closed (x y : real) : positive x → positive y → positive (x * y) :=
begin
  assume hx hy,
  cases exists_rep x with a ha,
  cases exists_rep y with b hb,
  subst ha, subst hb,
  change positive ⟦a * b⟧,
  rw pos_cls rfl,
  rw pos_cls rfl at hx,
  rw pos_cls rfl at hy,
  cases hx with ε hx,
  cases hx with hε hx,
  cases hx with N hN,
  cases hy with δ hy,
  cases hy with hδ hy,
  cases hy with M hM,
  existsi ε * δ,
  split, {
    apply pos_mul_pos; assumption,
  }, {
    existsi mynat.max M N,
    intros n hn,
    rw cau_seq.mul_val,
    have hM₁ := hM n (mynat.max_le_cancel_left hn),
    have hN₁ := hN n (mynat.max_le_cancel_right hn),
    apply lt_mul_comb_nonneg,
    any_goals { {apply lt_impl_le, assumption} <|> assumption, },
  },
end

private theorem zero_nonpos : ¬positive (0 : real) := sorry

private theorem neg_pos_impl_nonpos (x : real) : positive (-x) → ¬positive x :=
begin
  assume hx,
  cases exists_rep x with a ha,
  subst ha,
  rw neg_eq_cls rfl at hx,
  rw pos_cls rfl at hx,
  rw pos_cls rfl,
  rw not_exists,
  have ha := a.property,
  unfold is_cau_seq at ha,
  intro ε,
  rw not_and,
  intro hε,
  rw not_exists,
  intros N,
  rw not_forall,
  cases hx with δ hx,
  cases hx with hδ hx,
  cases hx with M hM,
  have := ha (ε + δ) _, {
    cases this with K hK,
    existsi N.max K,
    rw not_imp,
    split, {
      apply mynat.max_le_left,
    }, {
      change ¬¬ _ ≤ ε,
      rw not_not,
      rw le_neg_switch_iff,
      have h₁ := hK (N.max K) (M.max K) mynat.max_le_right mynat.max_le_right,
      have h₂ := hM (M.max K) mynat.max_le_left,
      clear ha hM hK,
      rw cau_seq.neg_val at h₂,
      apply lt_impl_le,
      rw ←myring.add_zero (-ε),
      rw ←neg_add δ,
      rw ←myring.add_assoc,
      rw ←myring.add_zero (-a.val _),
      rw ←myring.add_neg (a.val (M.max K)),
      rw ←myring.add_assoc,
      apply lt_comb, {
        rw ←neg_distr,
        rw add_comm (-_),
        rw ←sub_def,
        apply abs_lt_left,
        assumption,
      }, {
        assumption,
      },
    },
  }, {
    rw ←zero_add (0 : myrat),
    apply lt_comb; assumption,
  },
end

-- And partial converse
private theorem nzero_npos_impl_neg_pos {x : real} : x ≠ 0 → ¬positive x → positive (-x) :=
begin
  intros hx0 hx,
  cases exists_rep x with a ha,
  subst ha,
  sorry,
end

def le (x y : real) := ¬positive (x - y)

instance: has_le real := ⟨le⟩

local attribute [instance] classical.prop_decidable

variables x y z : real

private theorem le_add_right : x ≤ y → x + z ≤ y + z :=
begin
  cases exists_rep x with a ha,
  cases exists_rep y with b hb,
  cases exists_rep z with c hc,
  intros hxy,
  subst ha, subst hb, subst hc,
  change ¬positive (⟦a⟧ - ⟦b⟧) at hxy,
  change ¬positive ((⟦a⟧ + ⟦c⟧) - (⟦b⟧ + ⟦c⟧)),
  rw sub_def at *,
  rw neg_distr,
  rw add_assoc,
  -- Super useful trick to avoid `conv`
  -- Supply the *form* of the desired terms, let Lean figure out the _
  rw add_comm _ (-_ + -_),
  rw add_assoc (-_),
  rw neg_add,
  rw add_zero,
  assumption,
end

private theorem zero_le_mul : 0 ≤ x → 0 ≤ y → 0 ≤ x * y :=
begin
  intros hx hy,
  by_cases hx0 : x = 0, {
    rw [hx0, zero_mul],
    change ¬positive (0 - 0),
    rw sub_zero,
    exact zero_nonpos,
  },
  by_cases hy0 : y = 0, {
    rw [hy0, mul_zero],
    change ¬positive (0 - 0),
    rw sub_zero,
    exact zero_nonpos,
  }, {
    have : x * y ≠ 0,
      apply mul_nzero; assumption,
    cases exists_rep x with a ha,
    cases exists_rep y with b hb,
    subst ha, subst hb,
    change ¬positive (0 - ⟦a⟧ * ⟦b⟧),
    change ¬positive (0 - ⟦a⟧) at hx,
    change ¬positive (0 - ⟦b⟧) at hy,
    rw zero_sub at *,
    apply neg_pos_impl_nonpos,
    rw neg_neg,
    apply pos_mul_closed,
    all_goals {
      -- Give lean a vague helping hand
      rw ←@neg_neg real _ ⟦_⟧,
      apply nzero_npos_impl_neg_pos,
        assume h,
        rw ←neg_neg (0 : real) at h,
        rw ←neg_eq at h,
        rw neg_zero at h,
        contradiction,
      assumption,
    },
  },
end

private theorem le_trans : x ≤ y → y ≤ z → x ≤ z :=
begin
  assume hxy hyz,
  by_cases hxeqy : x - y = 0, {
    rw sub_to_zero_iff_eq at hxeqy,
    subst hxeqy,
    assumption,
  },
  by_cases hyeqz : y - z = 0, {
    rw sub_to_zero_iff_eq at hyeqz,
    subst hyeqz,
    assumption,
  },
  cases exists_rep x with a ha,
  cases exists_rep y with b hb,
  cases exists_rep z with c hc,
  subst ha, subst hb, subst hc,
  change ¬positive (⟦a⟧ - ⟦c⟧ : real),
  change ¬positive (⟦a⟧ - ⟦b⟧ : real) at hxy,
  change ¬positive (⟦b⟧ - ⟦c⟧ : real) at hyz,
  have hxy2 := nzero_npos_impl_neg_pos hxeqy hxy,
  have hyz2 := nzero_npos_impl_neg_pos hyeqz hyz,
  clear hxeqy hyeqz hxy hyz,
  apply neg_pos_impl_nonpos,
  rw [sub_def, neg_distr, neg_neg] at *,
  rw ←add_zero (-_),
  rw ←add_neg ⟦b⟧,
  rw ←add_assoc,
  rw add_assoc,
  apply pos_add_closed; assumption,
end

private theorem le_total_order : x ≤ y ∨ y ≤ x :=
begin
  by_cases h : x ≤ y, {
    left, assumption,
  }, {
    right,
    change ¬positive (y - x),
    change ¬¬positive (x - y) at h,
    rw not_not at h,
    apply neg_pos_impl_nonpos,
    rwa neg_sub,
  },
end

private theorem le_antisymm : x ≤ y → y ≤ x → x = y :=
begin
  intros hxy hyx,
  by_cases h : x - y = 0, {
    rwa ←sub_to_zero_iff_eq,
  }, {
    exfalso,
    change ¬positive (x - y) at hxy,
    change ¬positive (y - x) at hyx,
    have := nzero_npos_impl_neg_pos h hxy,
    rw neg_sub at this,
    contradiction,
  },
end

instance: ordered_myfield real := ⟨
  by apply_instance,
  le_add_right,
  zero_le_mul,
  le_trans,
  le_total_order,
  le_antisymm
⟩

end real

end hidden