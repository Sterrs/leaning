-- boring propositional theorems

namespace hidden

variables p q: Prop

theorem mp_to_contrapositive: (p → q) → (¬q → ¬p) :=
begin
  assume hpq hnq hp,
  from hnq (hpq hp),
end

theorem iff_to_contrapositive: (p ↔ q) → (¬p ↔ ¬q) :=
begin
  assume hpq,
  split, {
    from mp_to_contrapositive _ _ hpq.mpr,
  }, {
    from mp_to_contrapositive _ _ hpq.mp,
  }
end

end hidden
