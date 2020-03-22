import .segment ..relations.congs

-- A circle is a point (the centre) and a
-- line segment (congruent to any radius)

structure circle :=
(O : point) -- centre
(r : segment) -- radius

def lies_on_circ (P : point) (c : circle)
: Prop := c.O↦P ≅ c.r

def tangent (ℓ : line) (c : circle) :
Prop :=
∃ P : point,
P⊏ℓ ∧ lies_on_circ P c ∧
(∀ Q : point, (Q⊏ℓ ∧ lies_on_circ Q c)
→ Q = P)

-- This is going to be really hard
