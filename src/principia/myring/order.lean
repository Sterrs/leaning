import .basic
import ..logic

namespace hidden

def a := decidable_linear_order

class ordered_myring (α : Type)
extends myring α, has_le α :=
(le_add_right (a b c : α) : a ≤ b → a + c ≤ b + c)
(zero_le_mul (a b : α) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
(le_trans (a b c: α): a ≤ b → b ≤ c → a ≤ c)
(le_total_order (a b: α): a ≤ b ∨ b ≤ a)
(le_antisymm (a b: α): a ≤ b → b ≤ a → a = b)

namespace ordered_myring

open myring

variables {α : Type} [ordered_myring α] (a b c d: α)

def lt : α → α → Prop := λ a b, ¬(b ≤ a)
instance: has_lt α := ⟨lt⟩

theorem le_add_cancel_right: a ≤ b ↔ a + c ≤ b + c :=
begin
  apply iff.intro (le_add_right _ _ _),
  assume hacbc,
  have := le_add_right _ _ (-c) hacbc,
  repeat {rw [myring.add_assoc, myring.add_neg, myring.add_zero] at this},
  assumption,
end

theorem le_add_left: a ≤ b → c + a ≤ c + b :=
begin
  repeat {rw add_comm c},
  from le_add_right _ _ _,
end

theorem le_add_cancel_left: a ≤ b ↔ c + a ≤ c + b :=
begin
  repeat {rw add_comm c},
  from le_add_cancel_right _ _ _,
end

theorem le_neg_switch: a ≤ b → -b ≤ -a :=
begin
  assume hab,
  rw le_add_cancel_right _ _ (a + b),
  rw add_comm (-b),
  rw add_assoc,
  rw add_neg,
  rw add_zero,
  rw ←add_assoc,
  rw neg_add,
  rw zero_add,
  assumption,
end

theorem le_neg_switch_iff: a ≤ b ↔ -b ≤ -a :=
begin
  apply iff.intro (le_neg_switch _ _),
  assume hba,
  rw ←neg_neg a,
  rw ←neg_neg b,
  from le_neg_switch _ _ hba,
end

theorem square_nonneg: 0 ≤ a * a :=
begin
  cases le_total_order 0 a with ha ha, {
    from zero_le_mul a a ha ha,
  }, {
    rw ←neg_mul_neg a a,
    rw le_neg_switch_iff at ha,
    rw neg_zero at ha,
    apply zero_le_mul; assumption,
  },
end

theorem zero_le_one: (0 : α) ≤ 1 :=
begin
  rw ←mul_one (1: α),
  from square_nonneg _,
end

@[refl]
theorem le_refl: a ≤ a :=
begin
  cases le_total_order a a; assumption,
end

theorem wlogle
(p: α → α → Prop)
(hsymm: ∀ m n: α, p m n → p n m):
(∀ m n: α, m ≤ n → p m n) → (∀ m n: α, p m n) :=
begin
  assume hwlog,
  intros m n,
  cases le_total_order m n with hmn hnm, {
    from hwlog m n hmn,
  }, {
    from hsymm _ _ (hwlog n m hnm),
  },
end

-- not sure what the most optimal way to do this is
@[trans]
private lemma le_trans_lemma: a ≤ b → b ≤ c → a ≤ c :=
le_trans _ _ _

theorem le_iff_diff_nonneg:
a ≤ b ↔ 0 ≤ b - a :=
begin
  have := le_add_cancel_right a b (-a),
  rw add_neg at this,
  from this,
end

theorem le_add_comb:
a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
  assume hab hcd,
  transitivity (a + d), {
    from le_add_left _ _ _ hcd,
  }, {
    from le_add_right _ _ _ hab,
  },
end

theorem le_mul_nonneg_left: 0 ≤ c → a ≤ b → c * a ≤ c * b :=
begin
  assume h0z hxy,
  rw le_iff_diff_nonneg,
  rw ←mul_sub,
  apply zero_le_mul, {
    assumption,
  }, {
    rw ←le_iff_diff_nonneg,
    assumption,
  },
end

-- this is a succ le succ original. very good vintage
theorem le_mul_nonneg_right: 0 ≤ c → a ≤ b → a * c ≤ b * c :=
λ hc hab, by rw [mul_comm, mul_comm b]; from le_mul_nonneg_left _ _ _ hc hab

theorem le_mul_comb_nonneg
(hx : 0 ≤ a) (hz : 0 ≤ c) (hxy : a ≤ b) (hzw : c ≤ d):
 a * c ≤ b * d :=
begin
  transitivity (b * c),
    apply le_mul_nonneg_right; assumption,
  apply le_mul_nonneg_left,
    transitivity a; assumption,
  assumption,
end

theorem le_mul_nonpos_left: c ≤ 0 → a ≤ b → c * b ≤ c * a :=
begin
  assume hz0 hxy,
  rw le_neg_switch_iff at hz0,
  rw le_neg_switch_iff at hxy,
  rw neg_zero at hz0,
  have := le_mul_nonneg_left _ _ _ hz0 hxy,
  repeat {rw neg_mul_neg at this},
  assumption,
end

theorem le_mul_nonpos_right : c ≤ 0 → a ≤ b → b * c ≤ a * c :=
λ hc hab, by rw [mul_comm, mul_comm a]; from le_mul_nonpos_left _ _ _ hc hab

-- probably not needed with `change` etc
theorem lt_iff_nle: a < b ↔ ¬b ≤ a := iff.rfl

theorem lt_impl_ne: a < b → a ≠ b :=
begin
  assume hxy hxeqy,
  subst hxeqy,
  apply hxy,
  refl,
end

theorem lt_nrefl: ¬(a < a) :=
begin
  assume h,
  from lt_impl_ne _ _ h rfl,
end

theorem lt_impl_le: a < b → a ≤ b :=
begin
  assume hxy,
  cases le_total_order a b with h h, {
    assumption,
  }, {
    contradiction,
  },
end

theorem lt_very_antisymmetric: ¬(a < b ∧ b < a) :=
begin
  assume h,
  cases h with hxy hyx,
  cases le_total_order a b; contradiction,
end

-- still works without decidability, so not the same at lt_impl_le
theorem lt_very_antisymm_impl: a < b → ¬(b < a) :=
begin
  assume hab hba,
  apply lt_very_antisymmetric a b,
  split; assumption,
end

theorem lt_neg_switch_iff: a < b ↔ -b < -a :=
iff_to_contrapositive (le_neg_switch_iff b a)

@[trans]
theorem lt_trans: a < b → b < c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ _ _ (lt_impl_le _ _ hab) (lt_impl_le _ _ hbc),
  have h := le_antisymm _ _ hac this,
  subst h,
  from lt_very_antisymmetric _ _ ⟨hbc, hab⟩,
end

-- only works in ordered integral domain
-- (consider lexicographic order on ℤ × ℤ)
theorem zero_lt_mul
(hID: a * b = 0 → a = 0 ∨ b = 0): 0 < a → 0 < b → 0 < a * b :=
begin
  assume hapos hbpos,
  assume hab0,
  have := le_mul_nonneg_right _ _ _ (lt_impl_le _ _ hapos) (lt_impl_le _ _ hbpos),
  rw zero_mul at this,
  rw mul_comm at this,
  have h0 := le_antisymm _ _ hab0 this,
  cases (hID h0) with ha hb,
  have hc := lt_impl_ne _ _ hapos,
  from hc ha.symm,
  have hc := lt_impl_ne _ _ hbpos,
  from hc hb.symm,
end

theorem lt_add_cancel_left: a < b ↔ c + a < c + b :=
iff_to_contrapositive (le_add_cancel_left _ _ _)

theorem lt_add_cancel_right: a < b ↔ a + c < b + c :=
iff_to_contrapositive (le_add_cancel_right _ _ _)

theorem lt_iff_diff_pos: a < b ↔ 0 < b - a :=
begin
  have := lt_add_cancel_right a b (-a),
  rw add_neg at this,
  from this,
end

theorem lt_mul_pos_right
(hID: ∀ a b: α, a * b = 0 → a = 0 ∨ b = 0):
0 < c → ∀ a b: α, a < b ↔ a * c < b * c :=
begin
  assume h0z,
  intros a b,
  split; assume h, {
    rw lt_iff_diff_pos,
    rw lt_iff_diff_pos at h,
    rw ←sub_mul,
    from zero_lt_mul _ _ (hID _ _) h h0z,
  }, {
    rw lt_iff_diff_pos,
    rw lt_iff_diff_pos at h,
    assume h0yx,
    rw ←sub_mul at h,
    cases le_total_order c 0 with hc hc, {
      contradiction,
    }, {
      apply h,
      rw le_neg_switch_iff,
      rw neg_zero,
      rw ←neg_mul,
      apply zero_le_mul, {
        rw le_neg_switch_iff at h0yx,
        rw neg_zero at h0yx,
        assumption,
      }, {
        assumption,
      },
    },
  },
end

theorem lt_mul_pos_left 
(hID: ∀ a b: α, a * b = 0 → a = 0 ∨ b = 0):
0 < c → ∀ a b : α, a < b ↔ c * a < c * b :=
begin
  assume h0z,
  intros a b,
  repeat {rw mul_comm c},
  apply lt_mul_pos_right, {
    from hID,
  }, {
    assumption,
  },
end

theorem lt_comb {a b c d: α}: a < b → c < d → a + c < b + d :=
begin
  assume hab hcd,
  transitivity a + d,
  rw ←lt_add_cancel_left,
  assumption,
  rw ←lt_add_cancel_right,
  assumption,
end

theorem lt_le_chain: a < b → b ≤ c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ _ _ (lt_impl_le _ _ hab) hbc,
  have h := le_antisymm  _ _ this hac,
  subst h,
  clear hac this,
  have := le_antisymm _ _ (lt_impl_le _ _ hab) hbc,
  subst this,
  from lt_nrefl _ hab,
end

theorem le_lt_chain: a ≤ b → b < c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ _ _ hab (lt_impl_le _ _ hbc),
  have h := le_antisymm _ _ this hac,
  subst h,
  clear hac this,
  have := le_antisymm _ _ (lt_impl_le _ _ hbc) hab,
  subst this,
  from lt_nrefl _ hbc,
end

theorem lt_le_comb {a b c d: α}: a < b → c ≤ d → a + c < b + d :=
begin
  assume hab hcd,
  apply le_lt_chain _ (a + d),
  rw ←le_add_cancel_left,
  assumption,
  rw ←lt_add_cancel_right,
  assumption,
end

-- worth a different type class?
-- condition is necessary since = makes
-- the trivial ring into an ordered ring
theorem nontrivial_zero_lt_one: (0: α) ≠ 1 → (0: α) < 1 :=
begin
  assume nontrivial h,
  from nontrivial (le_antisymm _ _ zero_le_one h),
end

theorem nontrivial_zero_lt_two: (0: α) ≠ 1 → (0: α) < 2 :=
begin
  assume nontrivial,
  change (0: α) < 1 + 1,
  rw ←add_zero (0: α),
  apply lt_comb; from nontrivial_zero_lt_one nontrivial,
end

-- can't figure out hot to make decidability a typeclass thing
-- if we do a separate typeclass for decidably ordered rings
-- eg so we can do max/abs, move this there
theorem le_iff_lt_or_eq
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
a ≤ b ↔ a < b ∨ a = b :=
begin
  split, {
    assume hxy,
    by_cases h: b ≤ a, {
      right,
      from  le_antisymm _ _ hxy h,
    }, {
      left,
      assumption,
    },
  }, {
    assume h,
    cases h with h1 h2, {
      from lt_impl_le _ _ h1,
    }, {
      rw h2,
    },
  },
end

theorem lt_trichotomy
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
a = b ∨ a < b ∨ b < a :=
begin
  by_cases h: a ≤ b, {
    rw le_iff_lt_or_eq at h,
    cases h with h h, {
      right, left, assumption,
    }, {
      left, assumption,
    },
  }, {
    right, right, assumption,
  },
end

-- basically de Morgan
theorem lt_iff_le_and_neq
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  split, {
    assume h,
    split, {
      from lt_impl_le _ _ h,
    }, {
      from lt_impl_ne _ _ h,
    },
  }, {
    assume h,
    rw le_iff_lt_or_eq at h,
    cases h with h1 h2,
    cases h1 with h h, {
      assumption,
    }, {
      contradiction,
    },
  },
end

-- maybe we want to go and put this in a more general theory
-- of ordered abelian groups or something ;)
def abs [decidable_le: ∀ a b: α, decidable (a ≤ b)]:
α → α := (λ a, if 0 ≤ a then a else -a)

instance decidable_lt [decidable_le: ∀ a b: α, decidable (a ≤ b)]:
∀ a b: α, decidable (a < b) :=
λ a b, not.decidable

def sign [decidable_le: ∀ a b: α, decidable (a ≤ b)]
(a: α): α :=
if 0 < a then 1
  else if a < 0 then -1
    else 0

theorem abs_eq_plusminus
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
abs a = a ∨ abs a = -a :=
begin
  unfold abs,
  by_cases 0 ≤ a, {
    left,
    rw if_pos h,
  }, {
    right,
    rw if_neg h,
  },
end

theorem abs_zero
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
abs (0: α) = 0 :=
begin
  cases abs_eq_plusminus (0: α), {
    assumption,
  }, {
    rw neg_zero at h,
    assumption,
  },
end

theorem abs_neg
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
abs (-a) = abs a :=
begin
  unfold abs,
  by_cases ha: 0 ≤ a, {
    rw if_pos ha,
    by_cases ha2: 0 ≤ -a, {
      rw le_neg_switch_iff at ha2,
      rw [neg_zero, neg_neg] at ha2,
      rw ←(le_antisymm _ _ ha ha2),
      rw neg_zero,
      from abs_zero,
    }, {
      rw if_neg ha2,
      rw neg_neg,
    },
  }, {
    rw if_neg ha,
    by_cases ha2: 0 ≤ -a, {
      rw if_pos ha2,
    }, {
      rw le_neg_switch_iff at ha2,
      rw [neg_zero, neg_neg] at ha2,
      exfalso,
      from lt_very_antisymmetric _ _ ⟨ha, ha2⟩,
    },
  },
end

theorem abs_nonneg
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
0 ≤ abs a :=
begin
  unfold abs,
  by_cases ha: 0 ≤ a, {
    rw if_pos ha,
    assumption,
  }, {
    rw if_neg ha,
    apply lt_impl_le,
    rw lt_neg_switch_iff,
    rw [neg_neg, neg_zero],
    assumption,
  },
end

theorem le_self_abs
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
a ≤ abs a :=
begin
  unfold abs,
  by_cases ha: 0 ≤ a, {
    rw if_pos ha,
  }, {
    rw if_neg ha,
    transitivity (0: α), {
      apply lt_impl_le,
      assumption,
    }, {
      rw le_neg_switch_iff,
      rw [neg_neg, neg_zero],
      apply lt_impl_le,
      assumption,
    },
  },
end

theorem triangle_ineq
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
abs (a + b) ≤ abs a + abs b :=
begin
  unfold abs,
  by_cases hab: 0 ≤ a + b, {
    rw if_pos hab,
    apply le_add_comb, {
      from le_self_abs _,
    }, {
      from le_self_abs _,
    },
  }, {
    rw if_neg hab,
    rw neg_distr,
    apply le_add_comb, {
      transitivity abs (-a), {
        from le_self_abs _,
      }, {
        rw abs_neg,
        refl,
      },
    }, {
      transitivity abs (-b), {
        from le_self_abs _,
      }, {
        rw abs_neg,
        refl,
      },
    },
  },
end

theorem abs_lt_iff_lt_both
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
abs a < b ↔ -b < a ∧ a < b :=
begin
  split; assume h, {
    split, {
      rw lt_neg_switch_iff,
      rw neg_neg,
      apply le_lt_chain _ (abs a), {
        rw ←abs_neg,
        from le_self_abs _,
      }, {
        assumption,
      },
    }, {
      apply le_lt_chain _ (abs a), {
        from le_self_abs _,
      }, {
        assumption,
      },
    },
  }, {
    cases (abs_eq_plusminus a) with habs habs; rw habs, {
      from h.right,
    }, {
      rw lt_neg_switch_iff,
      rw neg_neg,
      from h.left,
    },
  },
end

theorem abs_lt_left
[decidable_le: ∀ a b: α, decidable (a ≤ b)]: abs a < b → -b < a :=
λ h, by rw abs_lt_iff_lt_both at h; from h.left

theorem abs_lt_right
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
abs a < b → a < b :=
λ h, by rw abs_lt_iff_lt_both at h; from h.right

theorem lt_abs_impl_lt_either
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
a < abs b → b < -a ∨ a < b :=
begin
  assume hab,
  cases abs_eq_plusminus b with h h, {
    rw ←h,
    right, assumption,
  }, {
    left,
    rw lt_neg_switch_iff,
    rw neg_neg,
    rw ←h,
    assumption,
  },
end

-- abs_diff refers to the pattern `abs (a - b) < c` which often shows up in analysis

theorem abs_diff_lt_left
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
abs (a - b) < c → b - c < a :=
begin
  assume h,
  have habs := abs_lt_left _ _ h,
  rw lt_add_cancel_left _ _ (-b),
  conv {
    congr, {
      change -b + (b + -c),
      rw ←add_assoc,
      rw neg_add,
      rw zero_add,
    }, {
      rw add_comm,
    },
  },
  from habs,
end

theorem abs_diff_lt_right
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
abs (a - b) < c → a < b + c :=
begin
  assume h,
  rw lt_neg_switch_iff,
  rw ←abs_neg at h,
  change abs (-(a + -b)) < c at h,
  rw neg_distr at h,
  rw neg_distr,
  from abs_diff_lt_left _ _ _ h,
end

theorem pos_sign
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
0 < a → sign a = 1 :=
begin
  assume h0a,
  unfold sign,
  rw if_pos h0a,
end

theorem neg_sign
[decidable_le: ∀ a b: α, decidable (a ≤ b)]:
a < 0 → sign a = -1 :=
begin
  assume ha0,
  unfold sign,
  rw if_neg (lt_very_antisymm_impl _ _ ha0),
  rw if_pos ha0,
end

end ordered_myring

end hidden