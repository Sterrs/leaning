import .add
import .le

namespace hidden
namespace myint

theorem intduction (p : myint → Prop) :
p 0 → (∀ {n}, p n → p (n + 1)) → (∀ {n}, p n → p (n - 1)) →
∀ n, p n :=
begin
  assume h0 hnext hprev,
  intro n,
  cases @le_total_order 0 n with h0n hn0, {
    rw le_iff_exists_nat at h0n,
    cases h0n with d hd,
    simp at hd,
    subst hd,
    induction d with n hn, {
      from h0,
    }, {
      from hnext hn,
    },
  }, {
    rw le_iff_exists_nat at hn0,
    cases hn0 with d hd,
    have: n = -↑d, {
      rw ←add_cancel ↑d,
      rw neg_self_add,
      symmetry, assumption,
    },
    subst this,
    clear hd,
    induction d with n hn, {
      from h0,
    }, {
      from hprev hn,
    },
  },
end

theorem intduction_from {m : myint} (p : myint → Prop):
(∀ {n}, p n → p (n + 1)) → (∀ {n}, p n → p (n - 1)) →
p m → ∀ n, p n :=
begin
  assume hnext hprev hex,
  suffices : p 0,
    apply intduction, repeat {assumption},
  revert m,
  apply intduction (λ m, p m → p 0), {
    assume h, assumption,
  }, {
    intro n,
    assume h,
    assume hpsn,
    have := hprev hpsn,
    rw sub_def at this,
    rw add_assoc at this,
    rw self_neg_add at this,
    rw add_zero at this,
    from h this,
  }, {
    intro n,
    assume h,
    assume hpsn,
    have := hnext hpsn,
    rw sub_def at this,
    rw add_assoc at this,
    rw neg_self_add at this,
    rw add_zero at this,
    from h this,
  },
end

end myint
end hidden
