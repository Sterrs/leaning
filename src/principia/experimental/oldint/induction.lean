import .add
import principia.mynat.induction

namespace hidden
namespace oldint

theorem intduction (p : oldint → Prop) :
p 0 → (∀ {n}, p n → p (n + 1)) → (∀ {n}, p n → p (n - 1)) →
∀ n, p n :=
begin
  assume h0 hnext hprev,
  intro n,
  cases n, {
    induction n with n hn, {
      rwa [mynat.zz, ←coe_nat_eq, zero_nat],
    }, {
      rw ←coe_nat_eq at hn,
      have h := hnext hn,
      rwa [←coe_nat_eq], -- magic?
    },
  }, {
    induction n with n hn, {
      rw [mynat.zz, ←neg_one],
      apply @hprev 0,
      assumption,
    }, {
      rw [←neg_coe_succ, ←mynat.add_one_succ, ←nat_nat_add, neg_distr,
          one_nat, ←sub_add_neg],
      apply @hprev (-↑(mynat.succ n)),
      rwa neg_coe_succ,
    },
  },
end

open mynat
private theorem one: (1: mynat) = succ 0 := rfl

theorem intduction_from {m : oldint} (p : oldint → Prop):
(∀ {n}, p n → p (n + 1)) → (∀ {n}, p n → p (n - 1)) →
p m → ∀ n, p n :=
begin
  assume hnext hprev hex,
  suffices : p 0,
    apply intduction, repeat {assumption},
  cases m, {
    revert m,
    apply descend_to_zero,
    intro m,
    assume hsucc,
    have := hprev hsucc,
    rwa [sub_add_neg, neg_one, ←coe_nat_eq, nat_neg_add, sub_succ_succ,
         nat_sub_zero] at this,
  }, {
    suffices : p (-1), from hnext this,
    rw neg_one,
    revert m,
    apply descend_to_zero,
    intro m,
    assume hsucc,
    have := hnext hsucc,
    rwa [←one_nat, neg_nat_add, one, sub_succ_succ, zero_sub_neg,
        neg_succ] at this,
  },
end

end oldint
end hidden
