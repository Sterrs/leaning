-- Just playing around with showing various equivalences of classical
-- assumptions in (intuitionist) natural deduction.

-- Written in tactic style because my Brian is too small for proper Lean

-- double negation elimination
def dne := ∀ p: Prop, ¬¬p → p
-- law of excluded middle
def lem := ∀ p: Prop, p ∨ ¬p
-- de Morgan's laws TODO
def dml_nor_and_left_t := ∀ p q: Prop, ¬(p ∨ q) → ¬p ∧ ¬q
def dml_nor_and_right_t := ∀ p q: Prop, ¬p ∧ ¬q → ¬(p ∨ q)
def dml_nor_and_t :=  ∀ p q: Prop, ¬(p ∨ q) ↔ ¬p ∧ ¬q
def dml_nand_or_left_t := ∀ p q: Prop, ¬(p ∧ q) → ¬p ∨ ¬q
def dml_nand_or_right_t := ∀ p q: Prop, ¬p ∨ ¬q → ¬(p ∧ q)
def dml_nand_or_t :=  ∀ p q: Prop, ¬(p ∨ q) ↔ ¬p ∧ ¬q

theorem lem_impl_dne: lem → dne :=
begin
    assume hlem,
    intro p,
    assume hnnp,
    have hpnp := hlem p,
    -- Quicker, but is `cases` constructive?
    -- cases hpnp with hp hnp,
    -- exact hp,
    -- contradiction,
    apply or.elim hpnp,
    intro p, from p,
    intro hnp,
    contradiction,
end

theorem dne_impl_lem: dne → lem :=
begin
    assume hdne,
    intro p,
    suffices hnn: ¬¬(p ∨ ¬p),
    from hdne (p ∨ ¬p) hnn,
    assume hnpnp,

    have hnp: ¬p,
    assume hp,
    have hpnp: p ∨ ¬p,
    left, from hp,
    contradiction,
    have hpnp: p ∨ ¬p,
    right, from hnp,
    contradiction,
end

theorem noncontradiction (p: Prop): ¬ (p ∧ ¬ p) :=
begin
    assume hpnp,
    have hp := hpnp.left,
    have hnp := hpnp.right,
    contradiction,
end

theorem dml_nor_and_left: dml_nor_and_left_t :=
begin
    intros p q,
    assume hnpq,
    split,
    intro hp,
    have hpq: p ∨ q := or.inl hp,
    contradiction,
    intro hq,
    have hpq: p ∨ q := or.inr hq,
    contradiction,
end

-- Not sure what's going on here.
theorem lem_impl_morgan_right: lem → dml_nor_and_right_t :=
begin
    assume hlem,
    intros p q,
    assume hnpnq,
    have hnp := hnpnq.left,
    have hnq := hnpnq.right,
    intro hpq,
    sorry,
end
