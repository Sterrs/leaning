import ..logic
import .le

namespace hidden
namespace myint

open myint
open myring
open ordered_myring

variables m n k : myint
variables a b c : mynat

instance decidable_lt: ∀ m n: myint, decidable (m < n) :=
λ a b, not.decidable

theorem lt_iff_succ_le: m < n ↔ m + 1 ≤ n :=
begin
  cases quotient.exists_rep m with a ha, subst ha,
  cases quotient.exists_rep n with b hb, subst hb,
  rw int_one,
  rw add_eq_cls rfl rfl,
  rw le_eq_cls rfl rfl,
  rw int_pair.le_def,
  rw int_pair.add_b,
  rw int_pair.add_a,
  conv in (a.a + (1: int_pair.int_pair).a + b.b) {
    rw mynat.add_assoc,
    rw mynat.add_comm _ b.b,
    rw ←mynat.add_assoc,
  },
  from mynat.lt_iff_succ_le,
end

end myint
end hidden
