-- NO CLASSICAL LOGIC HERE
section noclassical
  variables p q r: Prop

  -- commutativity of ∧
  example : p ∧ q ↔ q ∧ p :=
  begin
    apply iff.intro,

    assume h₁: p ∧ q,
    -- alternatively, "exact and.intro h₁.right h₁.left":
    exact ⟨h₁.right, h₁.left⟩,
    assume h₂: q ∧ p,
    exact ⟨h₂.right, h₂.left⟩,
  end
  -- commutativity of ∨
  example : p ∨ q ↔ q ∨ p :=
  begin
    apply iff.intro,

    assume h₁: p ∨ q,
    apply h₁.elim,
    assume hp₁: p,
    exact or.inr hp₁,
    assume hq₁: q,
    exact or.inl hq₁,

    assume h₂: q ∨ p,
    apply h₂.elim,
    assume hq₂: q,
    exact or.inr hq₂,
    assume hp₂: p,
    exact or.inl hp₂,
  end

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- negation
  example : p → ¬¬p :=
  begin
    assume hp: p,
    assume hnp: ¬p,
    exact absurd hp hnp,
  end

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) :=
  begin
    assume h: p ∧ ¬p,
    exact absurd h.left h.right,
  end
  example : p ∧ ¬q → ¬(p → q) :=
  begin
    assume (h₁: p ∧ ¬q) (h₂: p → q),
    exact absurd (h₂ h₁.left) h₁.right,
  end
  example : ¬p → (p → q) :=
  begin
    assume (hnp: ¬p) (hp: p),
    exact absurd hp hnp,
  end
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ false ↔ p := sorry
  example : p ∧ false ↔ false := sorry
  example : ¬(p ↔ ¬p) :=
  begin
    assume h: p ↔ ¬p,
    have hpnp, from h.mp,
    have hnpp, from h.mpr,
    sorry,
  end
  example : (p → q) → (¬q → ¬p) :=
  begin
    assume h: p → q,
    assume hnq: ¬q,
    assume hp: p,
    have hq: q, from h hp,
    exact absurd hq hnq,
  end
end noclassical

-- WARNING: CLASSICAL LOGIC BELOW
section classical
  open classical

  variables p q r s : Prop

  example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  -- trivial application of law of excluded middle
  example : p ∨ ¬p := em p
  example : (((p → q) → p) → p) := sorry
end classical