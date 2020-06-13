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

private theorem equivalent_trans: transitive equivalent :=
begin
    intros f g h,
    assume hfeqg hgeqh,
    intro ε,
    assume hepos,
    cases hfeqg (ε / 2) (myrat.half_pos hepos) with N1 hN1,
    cases hgeqh (ε / 2) (myrat.half_pos hepos) with N2 hN2,
    existsi max N1 N2,
    intro n,
    assume hN1N2n,
    have hN1e := hN1 n (max_lt_cancel_left hN1N2n),
    have hN2e := hN2 n (max_lt_cancel_right hN1N2n),
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
    rw myrat.half_plus_half at hcomb,
    from myrat.le_lt_chain _ _ _ this hcomb,
end

instance real_setoid: setoid cau_seq :=
⟨equivalent, equivalent_refl, equivalent_symm,
equivalent_trans⟩

theorem setoid_equiv (f g : cau_seq) :
f ≈ g ↔ equivalent f g := by refl

end cau_seq

end hidden
