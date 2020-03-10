axiom point : Type

-- Disclaimer:
-- Most of this is completely wrong, as there
-- should be a bunch of extra hypotheses exerting
-- that points/lines do not coincide.
-- It might be possible to prove false.
-- Lots of the axioms are missing, some types
-- are defined in the wrong way, some definitions
-- are suspicious

-- Basic definitions & axioms
-- See https://en.wikipedia.org/wiki/Hilbert's_axioms
-- TODO: Document the axioms properly in LaTeX

-- Ternary relation for points
axiom between : point → point → point → Prop

inductive line : Type
-- Construct the line between two distinct points
| mk (a b : point) (h : a ≠ b) : line

-- Relation between a point and a line
axiom lies_on : point → line → Prop

axiom line_eq (ℓ₁ ℓ₂ : line) :
ℓ₁ = ℓ₂ ↔
∀ (a : point) (h : lies_on a ℓ₁), lies_on a ℓ₂

-- Angle
structure angle := (ℓ₁ ℓ₂ : line)
-- Two angles are congruent if they are the same size
axiom cong_ang : angle → angle → Prop
-- Line segment
structure segment := (p₁ p₂ : point)
-- Two line segments are congruent if they are the same
-- length
axiom cong_seg : segment → segment → Prop

-- You lie on a segment iff you are between the endpoints
def lies_on_seg (p : point) (s : segment) : Prop :=
between s.p₁ p s.p₂
