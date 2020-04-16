import ..myint.lt

namespace hidden

open myint

structure frac :=
-- Numerator
(num : myint)
-- Denominator
(denom : myint)
-- Proof that the denominator is positive
(denom_pos : 0 < denom)

namespace frac

variables {x y z : frac}

-- Is this really necessary?
theorem num_and_denom_eq : x = y ↔ x.num = y.num ∧ x.denom = y.denom :=
begin
  split; assume h, {
    split,
    all_goals { congr, assumption, },
  }, {
    cases x,
    cases y,
    dsimp only [] at h,
    cases h with hnum hdenom,
    subst hnum,
    subst hdenom, -- Magic?
  },
end

end frac

end hidden
