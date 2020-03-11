import .basic

-- Two line segments are congruent if they are the same
-- length
axiom congs : segment → segment → Prop
infix `≅`:50 := congs

-- Two angles are congruent if they are the same size
axiom conga : angle → angle → Prop
infix `≅`:50 := conga
