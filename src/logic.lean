-- NO CLASSICAL LOGIC HERE
section noclassical
  variables p q r: Prop

  -- commutativity of ∧
  example : p ∧ q ↔ q ∧ p :=
  begin
    apply iff.intro,

    assume h₁: p ∧ q,
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

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) :=
  begin
    assume h: p ∧ ¬p,
    have hp: p, from and.left h,
    have hnp: ¬p, from and.right h,
    exact absurd hp hnp,
  end

  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ false ↔ p := sorry
  example : p ∧ false ↔ false := sorry
  example : ¬(p ↔ ¬p) := sorry
  example : (p → q) → (¬q → ¬p) := sorry
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
  example : p ∨ ¬p := em p
  example : (((p → q) → p) → p) := sorry
end classical