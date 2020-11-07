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

theorem exists_or {α : Type} {p q : α → Prop}:
(∃ k, p k ∨ q k) ↔ (∃ k, p k) ∨ (∃ k, q k) :=
begin
  split; assume h, {
    cases h with k h,
    cases h, {
      left,
      existsi k,
      assumption,
    }, {
      right,
      existsi k,
      assumption,
    },
  }, {
    cases h; cases h with k h, {
      existsi k,
      left,
      assumption,
    }, {
      existsi k,
      right,
      assumption,
    },
  }
end

universe u

@[simp]
theorem not_exists {α : Sort u} {p : α → Prop} :
(¬∃ x : α, p x) ↔ ∀ x : α, ¬p x :=
begin
  split; assume h,
    intro x,
    assume hpx,
    apply h,
    existsi x,
    assumption,
  assume hex,
  cases hex with x hpx,
  from h x hpx,
end

theorem not_and {p q : Prop} : ¬(p ∧ q) ↔ (p → ¬ q) :=
begin
  split; assume h,
    assume hp hq,
    from h ⟨hp, hq⟩,
  assume hpq,
  cases hpq with hp hq,
  from h hp hq,
end

open classical

@[simp]
theorem not_and_distrib {p q : Prop} : ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
begin
  split; assume h,
    cases em p with hp hnp,
      right,
      assume hq,
      from h ⟨hp, hq⟩,
    left, assumption,
  assume h,
  cases h with hp hq,
  cases h,
    from h hp,
  from h hq,
end

@[simp]
theorem not_not {p : Prop} : ¬¬p ↔ p :=
begin
  split; assume h,
    cases em p with hp hnp,
      assumption,
    contradiction,
  assume hnp,
  contradiction,
end

local attribute [instance] classical.prop_decidable

@[simp]
theorem not_forall {α : Sort u} {p : α → Prop} : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
begin
  split; assume h,
    by_contradiction hnex,
    simp at hnex,
    contradiction,
  assume hnall,
  cases h with x hnpx,
  have := hnall x,
  contradiction,
end

theorem not_imp {p q : Prop} : ¬(p → q) ↔ p ∧ ¬q :=
begin
  split; assume h, {
    split,
      cases em p with hp hnp,
        assumption,
      exfalso, from h (λ hp, (hnp hp).elim),
    assume hq,
    from h (λ hp, hq),
  }, {
    assume hpq,
    cases h with hp hnq,
    from hnq (hpq hp),
  },
end

end hidden
