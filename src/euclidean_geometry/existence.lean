import .relations.collinear

-- Proving the existence of certain things
open classical

-- Prove the existence of a point
-- I don't know if we can actually get the point
theorem there_is_a_point : ∃ (A : point), true :=
begin
  cases noncoll3 with A hA,
  constructor,
  assumption,
  trivial,
end

-- Given a point, there is a line through the point
theorem point_has_line (A : point) :
∃ ℓ : line, A ⊏ ℓ :=
begin
  cases noncoll3 with X h₁,
  cases h₁ with Y h₂,
  cases h₂ with Z hxyz,
  -- Better way to decompose complicated ∧ chain?
  have hxy, from hxyz.left,
  have h, from hxyz.right.right.right,
  cases em (A=X) with heq hneq,
    rw ←heq at hxy,
    cases line_containing hxy with ℓ hℓ,
    existsi ℓ,
    exact hℓ.left,

    cases line_containing hneq with ℓ hℓ,
    existsi ℓ,
    exact hℓ.left,
end

-- theorem not_on_line_imp_neq {A B : point} {ℓ : line}
-- (h₁ : A ⊏ ℓ) (h₂ : ¬ (B ⊏ ℓ)) :
-- A ≠ B := sorry

-- If three points are noncollinear then they are not equal
section
variables {A B C : point}
(h : ¬collinear A B C)

include A B C h

theorem ncoll_imp_neq13 : A ≠ C :=
begin
  assume h₁,
  rw h₁ at h,
  cases em (B=C) with heq hneq,
    rw ←heq at h,
    suffices : collinear B B B, contradiction,
    have := point_has_line B,
    cases this with ℓ hℓ,
    existsi ℓ,
    exact ⟨hℓ, ⟨hℓ, hℓ⟩⟩,
  cases line_containing hneq with ℓ hℓ,
  suffices : collinear C B C, contradiction,
  existsi ℓ,
  exact ⟨hℓ.right, ⟨hℓ.left, hℓ.right⟩⟩,
end
-- And symmetrically:
theorem ncoll_imp_neq12 : A ≠ B :=
begin
  have :=
    ncoll_symm12 (ncoll_symm13 (ncoll_symm12 h)),
  exact ncoll_imp_neq13 this,
end

theorem ncoll_imp_neq23 : B ≠ C :=
begin
  have := ncoll_symm12 h,
  exact ncoll_imp_neq13 this,
end
end

-- Given two points, there is a third which is
-- different to both and not on the line between them
theorem different_third_noncoll {A B : point} (distinct : A ≠ B):
∃ C : point, ¬ collinear A B C :=
begin
  cases noncoll3 with X h₁,
  cases h₁ with Y h₂,
  cases h₂ with Z hxyz,
  cases em (collinear A B X) with hX hnX,
    cases em (collinear A B Y) with hY hnY,
      cases em (collinear A B Z) with hZ hnZ,
        suffices : collinear X Y Z, cc,
        exact collinear_trans distinct hX hY hZ,
      existsi Z, assumption,
    existsi Y, assumption,
  existsi X, assumption,
end

-- Given two points, there is a line through one
-- but not the other
theorem point_has_own_line {A B : point} (distinct : A ≠ B):
∃ ℓ : line, A ⊏ ℓ ∧ ¬(B ⊏ ℓ) :=
begin
  have := different_third_noncoll distinct,
  cases this with C hC,
  have hnoncoll := hC,
  have hACneq := ncoll_imp_neq13 hC,
  cases line_containing hACneq with ℓ hℓ,
  existsi ℓ,
  split,
    exact hℓ.left,
  assume hBonℓ,
  have : collinear A B C,
  existsi ℓ,
  split,
    exact hℓ.left,
  split,
    exact hBonℓ,
  exact hℓ.right,
  contradiction,
end

-- Two points are equal exactly when every line through
-- one passes through the other
theorem point_eq {A B : point} :
A = B ↔
∀ (ℓ : line) (h: A ⊏ ℓ), B ⊏ ℓ :=
begin
  split,
    assume h ℓ hAℓ,
    rw ←h, assumption,
  assume h,
  apply by_contradiction,
  assume hneq,
  have := point_has_own_line hneq,
  cases this with ℓ hAnBℓ,
  have hABℓ := h ℓ,
  have := hABℓ hAnBℓ.left,
  have := hAnBℓ.right,
  contradiction,
end

-- Two lines are equal iff they share every point
theorem line_eq (ℓ₁ ℓ₂ : line) :
ℓ₁ = ℓ₂ ↔
∀ (X : point) (h : X ⊏ ℓ₁), X ⊏ ℓ₂
:=
begin
  apply iff.intro,
    assume h,
    intro X,
    assume hXonℓ₁,
    rw h at hXonℓ₁,
    assumption,
  assume h,
  have h₁ := two_points ℓ₁,
  cases h₁ with X h₂,
  cases h₂ with Y h₃,
  have hneq := h₃.left,
  have hXonℓ₁ := h₃.right.left,
  have hYonℓ₁ := h₃.right.right,
  have hXonℓ₂  := (h X) hXonℓ₁,
  have hYonℓ₂  := (h Y) hYonℓ₁,
  suffices : X⊏ℓ₁ ∧ X⊏ℓ₂ ∧ Y⊏ℓ₁ ∧ Y⊏ℓ₂,
    have h₄ := line_unique this,
    cases h₄ with hleq hpeq,
      assumption,
    contradiction,
  cc,
end
