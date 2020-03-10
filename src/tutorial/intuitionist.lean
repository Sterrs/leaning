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
    apply or.elim hpnp,
    intro p, from p,
    intro hnp,
    exfalso,
    from hnnp hnp,
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
    from or.inl hp,
    from hnpnp hpnp,
    have hpnp: p ∨ ¬p,
    from or.inr hnp,
    from hnpnp hpnp,
end

theorem noncontradiction (p: Prop): ¬ (p ∧ ¬ p) :=
begin
    assume hpnp,
    have hp := and.elim_left hpnp,
    have hnp := and.elim_right hpnp,
    exfalso,
    from hnp hp,
end

theorem dml_nor_and_left: dml_nor_and_left_t :=
begin
    intros p q,
    assume hnpq,
    apply and.intro,
    intro hp,
    have hpq: p ∨ q := or.inl hp,
    from hnpq hpq,
    intro hq,
    have hpq: p ∨ q := or.inr hq,
    from hnpq hpq,
end

theorem lem_impl_morgan_right: lem → dml_right :=
begin
    assume hlem,
    intros p q,
    assume hnpnq,
    have hnp := and.elim_left hnpnq,
    have hnq := and.elim_right hnpnq,
    intro hpq,
end
