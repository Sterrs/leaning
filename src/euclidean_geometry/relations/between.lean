import ..basic ..existence

-- Ternary relation for points
axiom between (A B C : point) :  Prop
notation A `∗` B `∗` C := between A B C

-- AXIOMS

-- If B is between A and C then B is between
-- C and A
@[simp]
axiom between_symm {A B C : point} (h : A∗B∗C) : C∗B∗A

-- If B is between A and C then B lies on any line
-- A and C both lie on
axiom between_imp_on_line {A B C : point} {ℓ : line}
(h : A∗B∗C) (hA : A ⊏ ℓ)
(hC : C ⊏ ℓ) : B ⊏ ℓ

-- There is certainly a point between any distinct
-- two other points
axiom point_between {A C : point} (h : A ≠ C) :
∃ B : point, A∗B∗C

-- If B is between A and C then
-- A is not between B and C and
-- C is not between A and B
axiom unique_order {A B C : point} :
(A∗B∗C) → ¬ (B∗A∗C) ∧ ¬ (A∗C∗B)

-- THEOREMS

open classical

-- Follows nicely from unique ordering
@[simp]
theorem between_non_refl12 {A B : point} :
¬(A∗A∗B) :=
begin
  assume h,
  have := unique_order h,
  have := this.left,
  contradiction,
end

-- Follows nicely from the previous
@[simp]
theorem between_non_refl23 {A B : point} :
¬(A∗B∗B) :=
begin
  assume h,
  have := between_symm h,
  exact between_non_refl12 this,
end

-- Does not follow nicely at all
@[simp]
theorem between_non_refl13 {A B : point} :
¬(A∗B∗A) :=
begin
  assume h,
  suffices : ∀ (ℓ : line), A ⊏ ℓ → B ⊏ ℓ,
    -- Here point_eq is a very difficult thm to prove
    have heq := point_eq.mpr this,
    rw heq at h,
    exact between_non_refl12 h,
  intros ℓ hA,
  exact between_imp_on_line h hA hA,
end

theorem between_imp_neq {A B C : point} :
(A∗B∗C) → A ≠ B ∧ B ≠ C :=
begin
  assume h,
  split,
    assume heq,
    rw heq at h,
    exact between_non_refl12 h,

    assume heq,
    rw heq at h,
    exact between_non_refl23 h,
end
