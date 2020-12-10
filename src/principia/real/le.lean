import .lt

namespace hidden

namespace real

def le (x y : real) := ¬y < x

instance: has_le real := ⟨le⟩

variables x y z : real

theorem lt_iff_nle : x < y ↔ ¬y ≤ x := iff.rfl

end real

end hidden
