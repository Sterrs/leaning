import .relations.collinear .objects.segment

-- Statement and theorems relating to Pasch's
-- axiom

-- Pasch's axiom
-- If a line cuts a triangle once, it must cut
-- it again
axiom pasch {ℓ : line} {A B C : point}
(nonco : ¬ collinear A B C)
(h : intersect_seg ℓ ⟨A, B⟩) :
intersect_seg ℓ ⟨B, C⟩ ∨ intersect_seg ℓ ⟨C, A⟩
