import ..myrat.lt
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
sorry

private theorem equivalent_symm: symmetric equivalent :=
sorry

private theorem equivalent_trans: transitive equivalent :=
sorry

instance real_setoid: setoid cau_seq :=
⟨equivalent, equivalent_refl, equivalent_symm,
equivalent_trans⟩

end cau_seq

end hidden
