import ..objects.angle ..existence

-- Congruence of angles

-- Two angles are congruent if they are the same size
axiom conga : angle → angle → Prop
infix `≅`: 60 := conga

@[trans]
axiom conga_trans {α β γ : angle} :
α ≅ β → β ≅ γ → α ≅ γ

-- Given an angle we can construct an angle from
-- a point w.r.t. a line which is congruent
-- axiom construct_conga (α : angle) {P : point} {ℓ : line}
-- (h : P ⊏ ℓ) :
-- ∃ l : line, α

@[refl]
theorem conga_refl {α : angle} :
α ≅ α :=
sorry

theorem suppsupp {α : angle} :
α.supplement.supplement ≅ α :=
begin
  suffices : α.supplement.supplement = α,
    -- Implicitly uses refl
    rw this,
  exact α.suppsupp,
end

namespace angle
def right (α : angle) : Prop :=
α.ℓ₁ ≠ α.ℓ₂ ∧ α ≅ supplement α
end angle
