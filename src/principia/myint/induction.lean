import .add

namespace hidden
namespace myint

theorem intduction (p : myint → Prop) :
p 0 → (∀ n, p n → p (n + 1)) → (∀ n, p n → p (n - 1)) →
∀ n, p n :=
begin
  assume h0 hnext hprev,
  intro n,
  cases n, {
    induction n with n hn, {
      rwa [zz, ←coe_nat_eq, zero_nat],
    }, {
      rw ←coe_nat_eq at hn,
      have h := hnext n hn,
      rwa [←coe_nat_eq], -- magic?
    },
  }, {
    induction n with n hn, {
      rw [zz, ←neg_one],
      apply hprev 0,
      assumption,
    }, {
      rw [←neg_coe_succ, ←add_one_succ, ←nat_nat_add, neg_distr,
          one_nat, ←sub_add_neg],
      apply hprev (-↑(mynat.succ n)),
      rwa neg_coe_succ,
    },
  },
end

theorem intduction_from (p : myint → Prop):
(∃ m, p m) → (∀ n, p n → p (n + 1)) → (∀ n, p n → p (n - 1)) →
∀ n, p n :=
begin
  assume hex hnext hprev,
end

end myint
end hidden
