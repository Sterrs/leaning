import .basic .relations.parallel
.relations.conga

-- Here I am going to attempt to prove the
-- parallel postulate, or equivalent

-- Corresponding (and alternate) angles are congruent
theorem corresponding_angles
{ℓ₁ ℓ₂ l : line}
(hpara : ℓ₁∥ℓ₂)
(hi₁ : intersect ℓ₁ l)
(hi₂ : intersect ℓ₂ l) :
∡ hi₁ ≅ ∡ hi₂ :=
sorry