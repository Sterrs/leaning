import ..relations.intersect

-- Angle
-- Lines need not be different, but they must
-- intersect
structure angle :=
{ℓ₁ ℓ₂ : line}
(hi : intersect ℓ₁ ℓ₂)
notation `∡` := angle.mk

namespace angle

variable (α : angle)

include α

-- A straight angle is 180 degrees
def straight : Prop := α.ℓ₁ = α.ℓ₂

-- The supplement of an angle is simply
-- the angle constructed with the lines
-- in the opposite order
def supplement : angle :=
begin
  apply @angle.mk α.ℓ₂ α.ℓ₁,
  apply intersect_symm,
  from α.hi,
end

-- The supplement of the supplement is the original
-- angle
theorem suppsupp :
α.supplement.supplement = α :=
begin
  cases α.supplement.supplement,
  sorry,
end

end angle
