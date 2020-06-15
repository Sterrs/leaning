import .add

namespace hidden

namespace cau_seq

def positive : cau_seq → Prop :=
λ f : cau_seq, ∃ ε : myrat,
0 < ε ∧ (∃ N : mynat, ∀ n, N < n → ε < f.val n)

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
      have hhalf_ε := hhalf_ε₁ (myrat.half_pos hε),
      clear hhalf_ε₁,
      cases hhalf_ε with M hM,
      existsi (ε / 2),
      split,
        from myrat.half_pos hε,
      existsi (mynat.max M N),
      intro n,
      assume hmax,
      have hf := hN n (mynat.max_lt_cancel_right hmax),
      have hfg := hM n (mynat.max_lt_cancel_left hmax),
      clear hmax hM hN M N hequiv,
      rw [myrat.lt_add_right (ε/2), myrat.half_plus_half],
    },
    {
      have := myrat.abs_diff_lt_right hfg,
      transitivity (f.val n); assumption,
    }, {
      have := myrat.abs_diff_lt_left hfg,
      rw [myrat.lt_add_right (ε/2), ←myrat.sub_add_neg, myrat.add_assoc,
          myrat.neg_self_add, myrat.add_zero] at this,
      transitivity (g.val n); assumption,
    },
end

end cau_seq

namespace real

def positive : real → Prop :=
quotient.lift cau_seq.positive cau_seq.positive_well_defined

-- Need subtraction, then x < y ↔ positive (x - y)

end real

end hidden
