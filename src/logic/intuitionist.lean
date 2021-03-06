-- Just playing around with showing various equivalences of classical
-- assumptions in (intuitionist) natural deduction.

-- Particularly I take some rules of inference and either prove them
-- intuitionistically or show that they are equivalent to the law of the
-- excluded middle, which is a useful weapon to use against intuitionists
-- ("How can you possibly reject the law of the excluded middle when that's
--   equivalent to double negation elimination?????")

-- double negation elimination
def dne_t := ∀ p: Prop, ¬¬p → p
-- law of excluded middle
def lem_t := ∀ p: Prop, p ∨ ¬p
-- law of weak excluded middle. Strictly less informative than the full law.
-- See also https://ncatlab.org/nlab/show/weak+excluded+middle
def lwem_t := ∀ p: Prop, ¬p ∨ ¬¬p
-- de Morgan's laws
-- (three of which are intuitionistically valid! spot the odd one out)
def dml_nor_and_right_t := ∀ p q: Prop, ¬(p ∨ q) → ¬p ∧ ¬q
def dml_nor_and_left_t := ∀ p q: Prop, ¬p ∧ ¬q → ¬(p ∨ q)
def dml_nand_or_right_t := ∀ p q: Prop, ¬(p ∧ q) → ¬p ∨ ¬q
def dml_nand_or_left_t := ∀ p q: Prop, ¬p ∨ ¬q → ¬(p ∧ q)
-- proof by contradiction and contraposition
def pf_by_contrapos_t := ∀ p q: Prop, (¬q → ¬p) → (p → q)
def pf_by_contradict_t := ∀ p q: Prop, ¬(p ∧ ¬q) → (p → q)
-- equivalence of implication with a related disjunction
-- (the left implication is actually intuitionistically valid)
def disj_equiv_right_t := ∀ p q: Prop, (p → q) → q ∨ ¬p
def disj_equiv_left_t := ∀ p q: Prop, q ∨ ¬p → (p → q)
-- law of noncontradiction (intuitionistically valid)
def noncontradiction_t := ∀ p: Prop, ¬(p ∧ ¬p)
-- ridiculous classical theorem
def iff_assoc_t := ∀ p q r: Prop, ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r))

-- Much of the reasoning here could be made more concise using tactics like
-- contradiction or cases, but my, admittedly perhaps shortsighted, vision is to
-- produce proofs that are as close as possible to natural deduction, so while
-- I'm using tactic mode for legibility/usability I'm imposing this slightly
-- weird ephemeral style.

-- For related reasons I prefer apply and.intro to split, etc.

theorem lem_impl_dne: lem_t → dne_t :=
begin
  assume hlem,
  intro p,
  assume hnnp,
  have hpnp := hlem p,
  apply or.elim hpnp, {
    intro p, from p,
  }, {
    intro hnp,
    apply false.elim, from hnnp hnp,
  },
end

theorem dne_impl_lem: dne_t → lem_t :=
begin
  assume hdne,
  intro p,
  suffices hnn: ¬¬(p ∨ ¬p), {
    from hdne (p ∨ ¬p) hnn,
  }, {
    assume hnpnp,
    have hnp: ¬p, {
      assume hp,
      have hpnp: p ∨ ¬p, {
        apply or.inl, from hp,
      },
      apply false.elim, from hnpnp hpnp,
    },
    have hpnp: p ∨ ¬p, {
      apply or.inr, from hnp,
    },
    apply false.elim, from hnpnp hpnp,
  },
end

theorem lem_impl_contrapos: lem_t → pf_by_contrapos_t :=
begin
  assume hlem,
  intros p q,
  assume hhnqnp,
  apply or.elim (hlem q), {
    intros hq _,
    from hq,
  }, {
    intros hnq hp,
    apply false.elim,
    from hhnqnp hnq hp,
  },
end

theorem contrapos_impl_lem: pf_by_contrapos_t → lem_t :=
begin
  assume hcpos,
  intro p,
  apply dne_impl_lem,
  intro q,
  assume hnnq,
  apply hcpos true q _ true.intro,
  assume hnq _,
  from hnnq hnq,
end

theorem lem_impl_contradict: lem_t → pf_by_contradict_t :=
begin
  assume hlem,
  intros p q,
  assume hnhpnq,
  apply or.elim (hlem q), {
    assume hq _,
    from hq,
  }, {
    assume hnq hp,
    apply false.elim,
    from hnhpnq (and.intro hp hnq),
  },
end

theorem contradict_impl_lem: pf_by_contradict_t → lem_t :=
begin
  assume hcontr,
  intro p,
  apply dne_impl_lem,
  intro q,
  assume hnnq,
  apply hcontr true q _ true.intro,
  assume hntnq,
  from hnnq (and.elim_right hntnq),
end

theorem lem_impl_disj_equiv_right: lem_t → disj_equiv_right_t :=
begin
  assume hlem,
  intros p q,
  assume hpq,
  apply or.elim (hlem p), {
    assume hp,
    from or.inl (hpq hp),
  }, {
    assume hnp,
    from or.inr hnp,
  },
end

theorem disj_equiv_right_impl_lem: disj_equiv_right_t → lem_t :=
begin
  assume hdjeq,
  intro p,
  apply hdjeq p p,
  assume hp, from hp,
end

theorem disj_equiv_left: disj_equiv_left_t :=
begin
  intros p q,
  assume hqnp,
  apply or.elim hqnp, {
    assume hq _, from hq,
  }, {
    assume hnp hp,
    apply false.elim, from hnp hp,
  },
end

theorem noncontradiction: noncontradiction_t :=
begin
  intro p,
  assume hpnp,
  have hp := hpnp.left,
  have hnp := hpnp.right,
  apply false.elim, from hnp hp,
end

theorem dml_nor_and_right: dml_nor_and_right_t :=
begin
  intros p q,
  assume hnpq,
  apply and.intro, {
    assume hp,
    have hpq: p ∨ q := or.inl hp,
    from hnpq hpq,
  }, {
    assume hq,
    have hpq: p ∨ q := or.inr hq,
    from hnpq hpq,
  },
end

theorem dml_nor_and_left: dml_nor_and_left_t :=
begin
  intros p q,
  assume hnpnq,
  have hnp := hnpnq.left,
  have hnq := hnpnq.right,
  assume hpq,
  apply or.elim hpq, {
    from hnp,
  }, {
    from hnq,
  },
end

theorem dml_nand_or_left: dml_nand_or_left_t :=
begin
  intros p q,
  assume hnpnq,
  assume hpq,
  have hp := and.elim_left hpq,
  have hq := and.elim_right hpq,
  apply or.elim hnpnq, {
    assume hnp,
    from hnp hp,
  }, {
    assume hnq,
    from hnq hq,
  },
end

-- this feels like a bit more of a case-bash than it needs to be
theorem lwem_impl_dml_nand_or_right: lwem_t → dml_nand_or_right_t :=
begin
  assume hlwem,
  intros p q,
  assume hnpq,
  apply or.elim (hlwem p), {
    assume hnp,
    from or.inl hnp,
  }, {
    assume hnnp,
    have hnq: ¬q, {
      assume hq,
      have hnp: ¬p, {
        assume hp,
        from hnpq (and.intro hp hq),
      },
      from hnnp hnp,
    },
    from or.inr hnq,
  },
end

theorem dml_nand_or_right_impl_lwem: dml_nand_or_right_t → lwem_t :=
begin
  assume hdml,
  intro p,
  from (hdml p ¬p) (noncontradiction p),
end

-- this can probably be done better. Currently a very mechanical
-- case-bash. In a sense it might be kind of inevitable if
-- you want to prove it naturally, since there are necessarily
-- a lot of constructors involved
-- It's kind of fun that basically there are only two cases
-- where the classical is needed
theorem lem_impl_iff_assoc: lem_t → iff_assoc_t :=
begin
  assume hlem,
  intros p q r,
  have hright: ∀ p q r: Prop, (p ↔ q ↔ r) → (p ↔ (q ↔ r)), {
    intros p q r,
    assume hpqr,
    apply iff.intro, {
      assume hp,
      apply iff.intro, {
        assume hq,
        apply hpqr.mp,
        apply iff.intro, {
          assume _,
          from hq,
        }, {
          assume _,
          from hp,
        },
      }, {
        assume hr,
        from (hpqr.mpr hr).mp hp,
      },
    }, {
      assume hqr,
      apply or.elim (hlem r), {
        assume hr,
        from (hpqr.mpr hr).mpr (hqr.mpr hr),
      }, {
        assume hnr,
        apply or.elim (hlem p), {
          assume hp,
          from hp,
        }, {
          assume hnp,
          -- forward contrapositives
          have hnq: ¬q, {
            assume hq,
            from hnr (hqr.mp hq),
          },
          have hnpq: ¬(p ↔ q), {
            assume hpq,
            from hnr (hpqr.mp hpq),
          },
          apply false.elim, apply hnpq,
          apply iff.intro, {
            assume hp,
            apply false.elim, from hnp hp,
          }, {
            assume hq,
            apply false.elim, from hnq hq,
          },
        },
      },
    },
  },
  apply iff.intro, {
    from hright p q r,
  }, {
    assume hpqr,
    from (hright _ _ _ ((hright _ _ _ hpqr.symm).symm)).symm,
  },
end

theorem iff_assoc_impl_lem: iff_assoc_t → lem_t :=
begin
  assume hiff,
  apply dne_impl_lem,
  intros p hnnp,
  -- this is exactly what we want to prove.
  -- now it's just a bit of case work to show equivalence
  have h := (hiff false false p).mpr,
  suffices hr: (false ↔ false ↔ p), {
    from hr.mp iff.rfl,
  }, {
    apply h,
    apply iff.intro, {
      from false.elim,
    }, {
      assume hnp,
      from hnnp hnp.mpr,
    },
  },
end
