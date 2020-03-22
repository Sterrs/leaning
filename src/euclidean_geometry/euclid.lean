import .relations.parallel

-- Statement and theorems relating to Euclid's Axiom

-- There's a unique line through p parallel to ℓ
-- This should allow us to prove the parallel postulate.
axiom euclid_exist {ℓ : line} {P : point}
(h : ¬ P ⊏ ℓ) :
∃ (a : line), P ⊏ a ∧ ℓ ∥ a
axiom euclid_unique {a₁ a₂ ℓ : line} {P : point}
(h : ¬ P ⊏ ℓ) (ha : P ⊏ a₁ ∧ a₁ ∥ ℓ)
(hb : P ⊏ a₂ ∧ a₂ ∥ ℓ) :
a₁ = a₂
