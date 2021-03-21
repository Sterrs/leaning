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
N < n → N < m → abs (f m - f n) < ε

-- Create the type of Cauchy sequences
def cau_seq := {f : sequence myrat // is_cau_seq f}

namespace cau_seq

-- Two cauchy sequences are equivalent if their difference
-- tends to zero
def equivalent (f g : cau_seq) : Prop :=
∀ ε : myrat, 0 < ε → ∃ N : mynat,
∀ n : mynat, N < n → abs (f.val n - g.val n) < ε

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
    have hN1e := hN1 n (mynat.max_lt_cancel_left hN1N2n),
    have hN2e := hN2 n (mynat.max_lt_cancel_right hN1N2n),
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

-- TODO bounded_above and bounded_below

theorem abs_bounded_above (f : cau_seq) :
∃ (u : myrat), 0 < u ∧ ∀ n, abs (f.val n) < u:=
begin
  sorry,
end

theorem nzero_impl_abs_eventually_bounded_below (f : cau_seq) (hf : ¬f ≈ 0) :
∃ (C : myrat) (N : mynat), 0 < C ∧ ∀ n : mynat, N < n → C < abs (f.val n) :=
begin
  sorry,
end

end cau_seq

end hidden
