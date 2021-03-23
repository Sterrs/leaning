import ..myrat.le
import ..myring.order
import ..mynat.max
import ..sequence

namespace hidden

open myring
open ordered_myring
open myfield
open ordered_myfield

def is_cau_seq (f : sequence myrat) : Prop :=
∀ ε : myrat, 0 < ε → ∃ N : mynat, ∀ n m : mynat,
N ≤ n → N ≤ m → abs (f m - f n) < ε

-- Create the type of Cauchy sequences
def cau_seq := {f : sequence myrat // is_cau_seq f}

namespace cau_seq

-- Two cauchy sequences are equivalent if their difference
-- tends to zero
def equivalent (f g : cau_seq) : Prop :=
∀ ε : myrat, 0 < ε → ∃ N : mynat,
∀ n : mynat, N ≤ n → abs (f.val n - g.val n) < ε

private theorem equivalent_refl: reflexive equivalent :=
begin
    intros f ε,
    assume hepos,
    cases f.property ε hepos with N hN,
    existsi N,
    intro n,
    assume hNn,
    from hN n n hNn hNn,
end

private theorem equivalent_symm: symmetric equivalent :=
begin
    intros f g,
    assume hfeqg,
    intro ε,
    assume hepos,
    cases hfeqg ε hepos with N hN,
    existsi N,
    intro n,
    assume hNn,
    have := hN n hNn,
    rwa [←abs_neg, sub_def, neg_distr, neg_neg, add_comm, ←sub_def],
end

private theorem equivalent_trans: transitive equivalent :=
begin
    intros f g h,
    assume hfeqg hgeqh,
    intro ε,
    assume hepos,
    cases hfeqg (ε / 2) (half_pos hepos) with N1 hN1,
    cases hgeqh (ε / 2) (half_pos hepos) with N2 hN2,
    existsi mynat.max N1 N2,
    intro n,
    assume hN1N2n,
    have hN1e := hN1 n (mynat.max_le_cancel_left hN1N2n),
    have hN2e := hN2 n (mynat.max_le_cancel_right hN1N2n),
    have := triangle_ineq (f.val n - g.val n) (g.val n - h.val n),
    conv at this {
      congr,
      rw [sub_def, sub_def, add_assoc],
      congr, congr, skip,
      rw ←add_assoc,
      congr,
      rw [add_comm, ←sub_def, sub_self],
    },
    rw [zero_add, ←sub_def] at this,
    have hcomb := lt_comb hN1e hN2e,
    rw half_plus_half at hcomb,
    apply le_lt_chain (abs (f.val n - g.val n) + abs (g.val n - h.val n)); assumption,
    assume water,
    apply nontrivial_zero_ne_two myrat.nontrivial,
    symmetry, assumption,
end

instance real_setoid: setoid cau_seq :=
⟨equivalent, equivalent_refl, equivalent_symm,
equivalent_trans⟩

theorem setoid_equiv (f g : cau_seq) :
f ≈ g ↔ equivalent f g := iff.rfl

theorem seq_eq_impl_eq (f g : cau_seq) : (∀ n, f.val n = g.val n) → f = g :=
begin
  cases f, cases g,
  dsimp only [],
  intros h,
  congr, -- Good old congr
  apply funext,
  assumption,
end

theorem seq_eq_impl_cau_seq_equiv (f g : cau_seq) : (∀ n, f.val n = g.val n) → f ≈ g :=
begin
  assume h,
  rw setoid_equiv,
  unfold equivalent,
  intros ε hε,
  existsi (0 : mynat),
  intros n hn,
  rwa [h n, sub_self],
end

theorem constant_cauchy (x : myrat) : is_cau_seq (λ n, x) :=
begin
  dsimp only [is_cau_seq],
  rw sub_self,
  intros ε hε,
  existsi (0 : mynat),
  intros m n hm hn,
  rwa abs_zero,
end

instance: has_zero cau_seq := ⟨⟨λ n, 0, constant_cauchy 0⟩⟩

instance: has_one cau_seq := ⟨⟨λ n, 1, constant_cauchy 1⟩⟩

local attribute [instance] classical.prop_decidable

theorem abs_bounded_above (f : cau_seq) :
∃ (u : myrat), 0 < u ∧ ∀ n, abs (f.val n) < u:=
begin
  cases f.property 1 (ordered_myring.nontrivial_zero_lt_one myrat.nontrivial) with N h,
  existsi max (1 + (max_upto N $ λ n, abs (f.val n))) (abs (f.val N) + 1),
  split, {
    apply lt_le_chain (abs (f.val N) + 1),
      rw ←add_zero (0 : myrat),
      apply le_lt_comb,
        exact abs_nonneg _,
      exact (ordered_myring.nontrivial_zero_lt_one myrat.nontrivial),
    apply ordered_myring.le_max_right,
  }, {
    intros n,
    have := h n N,
    by_cases hNn : N ≤ n, {
      have := this hNn (@mynat.le_refl N),
      apply lt_le_chain (abs (f.val N) + 1), {
        rw lt_add_cancel_left _ _ (-abs (f.val N)),
        rw add_comm,
        rw ←add_assoc,
        rw neg_add,
        rw zero_add,
        apply le_lt_chain (abs (f.val N - f.val n)), {
          transitivity abs (abs (f.val n) + -abs (f.val N)),
            apply self_le_abs,
          rw ←sub_def,
          rw abs_sub_switch,
          apply triangle_ineq_sub,
        }, {
          assumption,
        },
      }, {
        apply ordered_myring.le_max_right,
      },
    }, {
      change n < N at hNn,
      have hNn₂ := mynat.lt_impl_le hNn,
      apply lt_le_chain (1 + max_upto N (λ (n : mynat), abs (f.val n))), {
        rw ←zero_add (abs (f.val n)),
        apply lt_le_comb, {
          exact (ordered_myring.nontrivial_zero_lt_one myrat.nontrivial),
        }, {
          -- `change` comes into its own
          change ((λ (n : mynat), abs (f.val n)) n) ≤ _,
          apply max_upto_ge_before,
          assumption,
        },
      }, {
        apply ordered_myring.le_max_left,
      },
    },
  },
end

-- Why was this so hard ffs
theorem nzero_impl_abs_eventually_bounded_below (f : cau_seq) (hnf0 : ¬f ≈ 0) :
∃ (δ : myrat) (N : mynat), 0 < δ ∧ ∀ n : mynat, N ≤ n → δ < abs (f.val n) :=
begin
  change ¬(f.equivalent 0) at hnf0,
  unfold cau_seq.equivalent at hnf0,
  rw not_forall at hnf0,
  cases hnf0 with ε hnf0,
  rw not_imp at hnf0,
  cases hnf0 with hε hnf0,
  rw not_exists at hnf0,
  have hfcau := f.property (ε / 2) (half_pos hε),
  cases hfcau with N hfcau,
  existsi (ε / 2),
  existsi N,
  split,
    exact half_pos hε,
  intros n hn,
  have hfN := hnf0 N,
  rw not_forall at hfN,
  cases hfN with m hm,
  rw not_imp at hm,
  cases hm with hNm hm,
  change ¬abs (f.val m - 0) < ε at hm,
  rw [sub_def, neg_zero, myring.add_zero] at hm,
  have := hfcau _ _ hn hNm,
  change ¬¬ε ≤ abs (f.val m) at hm,
  rw not_not at hm,
  clear hnf0 hn hNm hfcau,
  -- This is why P ≠ NP
  rw ←abs_abs,
  rw ←myring.add_zero (abs (f.val n)),
  rw ←myring.neg_add (abs (f.val m)),
  rw ←myring.add_assoc,
  rw ←neg_neg (abs (f.val n)),
  rw add_comm _ (-abs _),
  rw ←abs_neg,
  rw neg_distr,
  rw neg_distr,
  rw neg_neg,
  rw neg_neg,
  rw ←sub_def,
  rw ←sub_def,
  apply lt_le_chain (abs (abs (abs (f.val m) - abs (f.val n)) - abs (abs (f.val m)))), {
    rw abs_abs,
    rw abs_sub_switch,
    apply lt_le_chain (abs (f.val m) - abs (abs (f.val m) - abs (f.val n))), {
      rw sub_def,
      rw ←minus_half myrat.two_nzero,
      rw sub_def,
      apply le_lt_comb, assumption, {
        rw ←lt_neg_switch_iff,
        apply le_lt_chain (abs (f.val m - f.val n)),
          exact triangle_ineq_sub _ _,
        assumption,
      },
    },
    exact self_le_abs _,
  },
  exact triangle_ineq_sub _ _,
end

end cau_seq

end hidden
