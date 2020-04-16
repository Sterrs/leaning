import .cau_seq

namespace hidden

def real := quotient cau_seq.real_setoid

namespace real

-- TODO: Move this. I just put it here so that ≤ would work in
-- completeness.lean
instance: has_le real := sorry

end real

end hidden
