-- Learning the universal quantifier ∀
section universal
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
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  begin
    assume h₁ h₂,
    assume x : α,
    exact h₁ x (h₂ x),
  end
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  begin
    assume h₁ x,
    apply or.elim h₁,

    assume h₂,
    exact or.inl (h₂ x),

    assume h₃,
    exact or.inr (h₃ x),
  end

  -- Exercise 2

  variable r : Prop

  example : α → ((∀ x : α, r) ↔ r) :=
  begin
    assume x : α,
    apply iff.intro,
    assume h₁,
    exact h₁ x,

    assume h₂,
    assume y : α,
    exact h₂,
  end
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

  -- Exercise 3

  variables (men : Type) (barber : men)
  variable  (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false :=
  begin
    have h₁, from h barber,
    suffices hs: ¬shaves barber barber, from absurd (h₁.mpr hs) hs,
    assume hns,
    exact absurd hns (h₁.mp hns),
  end
end universal


-- Learning the existential quantifier ∃
section existential
  open classical

  variables (α : Type) (p q : α → Prop)
  variable a : α
  variable r : Prop

  example : (∃ x : α, r) → r :=
  begin
    assume h,
    exact match h with ⟨l, r⟩ := r end,
  end
  example (a : α) : r → (∃ x : α, r) :=
  begin
    assume hr,
    apply exists.intro,
    exact a,
    exact hr,
  end
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  iff.intro
    (assume h,
    match h with ⟨b, hb⟩ := ⟨⟨b, hb.left⟩, hb.right⟩ end)
    (assume h, have h1 : (∃ x, p x), from h.left,
    have h2: r, from h.right,
    match h1 with ⟨b, hb⟩ := ⟨b,⟨hb, h2⟩⟩ end)
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  begin
    apply iff.intro,
    assume h,
    apply exists.elim h,
    assume w hw,
    apply or.elim hw,
    assume hp,
    exact or.inl ⟨w, hp⟩,
    assume hq,
    exact or.inr ⟨w, hq⟩,

    assume h,
    apply or.elim h,
    assume hp,
    apply exists.elim hp,
    assume w hw,
    exact exists.intro w (or.inl hw),

    assume hq,
    apply exists.elim hq,
    assume w hw,
    exact exists.intro w (or.inr hw),
  end

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  begin
    apply iff.intro,
    assume h,
    assume he,
    apply exists.elim he,
    assume w,
    assume hw,
    exact absurd (h w) hw,

    assume h,
    intro x,
    apply by_contradiction,
    assume hnp,
    have : ∃ (x : α), ¬p x,
    exact ⟨x, hnp⟩,
    exact absurd this h,
  end
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  begin
    apply iff.intro,
    assume h,
    apply exists.elim h,
    assume w hw,
    assume ha,
    exact absurd hw (ha w),

    assume h,
    apply by_contradiction,
    assume h₁,
    have h₂ : ∀ (x : α), ¬ p x,
    intro x,
    assume hp,
    exact absurd (exists.intro x hp) h₁,

    show false, from absurd h₂ h,
  end
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
  theorem thm : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  begin
    -- non-constructive
    apply iff.intro,
    assume h,
    apply by_contradiction,
    assume hne,
    have ha : ∀ (x : α), p x,
    assume x,
    apply by_contradiction, -- Do we need two?
    assume hnp,
    have he, from exists.intro x hnp,
    exact absurd he hne,

    exact absurd ha h,

    -- constructive
    assume h₁,
    assume h₂,
    apply exists.elim h₁,
    assume w hw,
    exact absurd (h₂ w) hw,
  end
  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
  example : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  begin
    apply iff.intro,
    assume h hr,
    apply exists.elim h,
    assume w hw,
    exact ⟨w, hw hr⟩,

    sorry,
  end
end existential
