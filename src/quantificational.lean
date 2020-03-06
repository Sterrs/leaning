section quantifiers
  -- Exercise 1
  variables (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  begin
    apply iff.intro,
    assume h,
    apply and.intro,

    assume x : α,
    exact (h x).left,
    assume x: α,
    exact (h x).right,

    assume h,
    assume x : α,
    apply and.intro,
    exact h.left x,
    exact h.right x,
  end
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

  -- Exercise 2

  variable r : Prop

  example : α → ((∀ x : α, r) ↔ r) := sorry
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

  -- Exercise 3

  variables (men : Type) (barber : men)
  variable  (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
  sorry

end quantifiers