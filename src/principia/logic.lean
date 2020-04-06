-- vim: ts=2 sw=0 sts=-1 et ai tw=70

-- boring propositional theorems

namespace hidden

variables {p q: Prop}

-- kind of cute little fact.
-- Basically comes from equivalence of p → q → r and p ∧ q → r
theorem implication_of_neg_commutative: (p → ¬q) ↔ (q → ¬p) :=
begin
  split, {
    assume hpnq hq hp,
    from hpnq hp hq,
  }, {
    assume hqnp hp hq,
    from hqnp hq hp,
  },
end

theorem mp_to_contrapositive: (p → q) → (¬q → ¬p) :=
begin
  assume hpq hnq hp,
  from hnq (hpq hp),
end

theorem iff_to_contrapositive: (p ↔ q) → (¬p ↔ ¬q) :=
begin
  assume hpq,
  split, {
    from mp_to_contrapositive hpq.mpr,
  }, {
    from mp_to_contrapositive hpq.mp,
  }
end

end hidden
