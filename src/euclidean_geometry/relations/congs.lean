import ..objects.segment

-- Congruence of segments

-- AXIOMS

-- Two line segments are congruent if they are the same
-- length
axiom congs : segment → segment → Prop
infix `≅`:40 := congs

@[refl]
axiom congs_refl {s : segment} : s ≅ s
@[trans]
axiom congs_trans {s t u : segment} :
s ≅ t → t ≅ u → s ≅ u

-- What the fuck
-- Given a segment we can construct two segments from
-- a point on a line which are congruent
axiom construct_congs {P : point} {ℓ : line} (s : segment) :
P ⊏ ℓ →
∃ Q₁ Q₂ : point,
(Q₁ ≠ Q₂) ∧ (Q₁ ⊏ ℓ) ∧ (Q₂ ⊏ ℓ) ∧
(s ≅ P↦Q₁) ∧ (s ≅ P↦Q₂)

-- Non-overlapping segments AB BC, and similarly PQ QR,
-- If AB ≅ PQ & BC ≅ QR then AC ≅ PR
axiom segment_combination (A B C P Q R : point)
(hABC : disjoint (A↦B) (B↦C))
(hPQR : disjoint (P↦Q) (Q↦R)) :
A↦B ≅ P↦Q → B↦C ≅ Q↦R →
A↦C ≅ P↦R
