import ..myrat.lt
import ..myrat.mul
import ..mynat.max
import ..sequence

namespace hidden

def is_cau_seq (f : sequence myrat) : Prop :=
∀ ε : myrat, 0 < ε → ∃ N : mynat, ∀ n m : mynat,
N < n → N < m → myrat.abs (f m - f n) < ε

-- Create the type of Cauchy sequences
def cau_seq := {f : sequence myrat // is_cau_seq f}

namespace cau_seq

-- Two cauchy sequences are equivalent if their difference
-- tends to zero
def equivalent (f g : cau_seq) : Prop :=
∀ ε : myrat, 0 < ε → ∃ N : mynat,
∀ n : mynat, N < n → myrat.abs (f.val n - g.val n) < ε

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
    rw ←myrat.abs_neg,
    rw ←myrat.sub_add_neg,
    rw myrat.neg_add,
    rw myrat.neg_neg,
    rw myrat.add_comm,
    rw myrat.sub_add_neg,
    from this,
end

private theorem h_alf: (2⁻¹: myrat) > 0 := sorry
private theorem w_h_ole: (2⁻¹: myrat) + 2⁻¹ = 1 := sorry

private theorem equivalent_trans: transitive equivalent :=
begin
    intros f g h,
    assume hfeqg hgeqh,
    intro ε,
    assume hepos,
    -- is this the right notation
    cases hfeqg (ε * 2⁻¹) (myrat.lt_pos_mul _ _ hepos h_alf) with N1 hN1,
    cases hgeqh (ε * 2⁻¹) (myrat.lt_pos_mul _ _ hepos h_alf) with N2 hN2,
    existsi max N1 N2,
    intro n,
    assume hN1N2n,
    have hN1e := hN1 n (max_lt_cancel hN1N2n),
    rw max_comm at hN1N2n,
    have hN2e := hN2 n (max_lt_cancel hN1N2n),
    have := myrat.triangle_ineq (f.val n - g.val n) (g.val n - h.val n),
    conv at this {
      congr,
      rw ←myrat.sub_add_neg,
      rw ←myrat.sub_add_neg,
      rw myrat.add_assoc,
      congr, congr, skip,
      rw ←myrat.add_assoc,
      congr,
      rw myrat.add_comm,
      rw myrat.sub_add_neg,
      rw myrat.sub_self,
    },
    rw myrat.zero_add at this,
    rw myrat.sub_add_neg at this,
    have hcomb := myrat.lt_comb _ _ _ _ hN1e hN2e,
    rw ←myrat.mul_add at hcomb,
    rw w_h_ole at hcomb,
    rw myrat.mul_one at hcomb,
    from myrat.le_lt_chain _ _ _ this hcomb,
end

instance real_setoid: setoid cau_seq :=
⟨equivalent, equivalent_refl, equivalent_symm,
equivalent_trans⟩

end cau_seq

end hidden
