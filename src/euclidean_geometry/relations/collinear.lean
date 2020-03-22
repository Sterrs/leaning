import ..basic

-- AXIOMS & DEFINITIONS

-- Concept of three points being collinear
def collinear (A B C : point) : Prop :=
∃ (ℓ : line), A ⊏ ℓ ∧ B ⊏ ℓ ∧ C ⊏ ℓ

-- There exist three points not all on the same line
axiom noncoll3 :
∃ (X Y Z : point),
(X ≠ Y) ∧ (Y ≠ Z) ∧ (Z ≠ X) ∧ ¬ collinear X Y Z

-- THEOREMS

-- collinear symmetric in first two variables
theorem coll_symm12 {A B C : point} :
collinear A B C → collinear B A C :=
begin
  assume h,
  cases h with ℓ hℓ,
  existsi ℓ,
  cc,
end

-- noncollinear symmetric in first and last variables
theorem ncoll_symm12 {A B C: point} :
¬collinear A B C → ¬ collinear B A C :=
begin
  assume h₁ h₂,
  have := coll_symm12 h₂,
  contradiction,
end

-- collinear symmetric in first and last variables
theorem coll_symm13 {A B C : point} :
collinear A B C → collinear C B A :=
begin
  assume h,
  cases h with ℓ hℓ,
  existsi ℓ,
  cc,
end

-- noncollinear symmetric in first and last variables
theorem ncoll_symm13 {A B C: point} :
¬collinear A B C → ¬ collinear C B A :=
begin
  assume h₁ h₂,
  have := coll_symm13 h₂,
  contradiction,
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

open classical

theorem to_line_passes_coll
{A B C : point} (distinct : A ≠ B)
(h : collinear A B C) :
C ⊏ (line_through distinct) :=
begin
  cases h with ℓ₂ hℓ₂,
  suffices : (line_through distinct) = ℓ₂,
    rw this,
    exact hℓ₂.right.right,
  have he := line_containing distinct,
  have hon := some_spec he,
  suffices : (line_through distinct) = (some he),
    rw this,
    apply @lines_equal
      A B (some he) ℓ₂ distinct,
    split, from hon.left,
    split, from hℓ₂.left,
    split, from hon.right,
    from hℓ₂.right.left,
  refl,
end
