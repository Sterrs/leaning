import .basic .incidence

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

theorem noncoll_imp_neq {A B C : point} (h : ¬ collinear A B C)
: A ≠ C :=
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

-- A useful property of collinear points
@[simp]
lemma collinear_trans {A B X Y Z : point}
(distinct : A ≠ B) :
collinear A B X → collinear A B Y → collinear A B Z
→ collinear X Y Z :=
begin
  cases line_containing distinct with ℓ hℓ,
  assume hX hY hZ,
  existsi ℓ,
  -- TODO: So much repetition!
  cases hX with ℓX hℓX,
  cases hY with ℓY hℓY,
  cases hZ with ℓZ hℓZ,
  have h₁ : ℓX = ℓ,
    have : A⊏ℓ ∧ A⊏ℓX ∧ B⊏ℓ ∧ B⊏ℓX,
      cc,
    have := line_unique this,
    cc,
  have h₂ : ℓY = ℓ,
    have : A⊏ℓ ∧ A⊏ℓY ∧ B⊏ℓ ∧ B⊏ℓY,
      cc,
    have := line_unique this,
    cc,
  have h₃ : ℓZ = ℓ,
    have : A⊏ℓ ∧ A⊏ℓZ ∧ B⊏ℓ ∧ B⊏ℓZ,
      cc,
    have := line_unique this,
    cc,
  cc,
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
        suffices : collinear X Y Z,
          have := hxyz.right.right.right,
          contradiction,
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
  have hACneq := noncoll_imp_neq hC,
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
