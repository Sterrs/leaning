import .basic
import ..mynat.lt
import ..logic

namespace hidden

class ordered_myring (α : Type) extends myring α, has_le α :=
(decidable_le: ∀ a b: α, decidable (a ≤ b))
(le_add_right {a b} (c : α) : a ≤ b → a + c ≤ b + c)
(zero_le_mul {a b : α} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
(le_trans {a} (b : α) {c}: a ≤ b → b ≤ c → a ≤ c)
(le_total_order (a b: α): a ≤ b ∨ b ≤ a)
(le_antisymm {a b: α}: a ≤ b → b ≤ a → a = b)

namespace ordered_myring

-- Add the [trans] attribute to le_trans
attribute [trans] le_trans

open myring

variables {α : Type} [ordered_myring α] (a b c d: α)

instance: ∀ a b: α, decidable (a ≤ b) := decidable_le

-- ≤ THEOREMS

theorem le_add_cancel_right : a ≤ b ↔ a + c ≤ b + c :=
begin
  apply iff.intro (le_add_right _),
  assume hacbc,
  have := le_add_right (-c) hacbc,
  repeat {rw [myring.add_assoc, myring.add_neg, myring.add_zero] at this},
  assumption,
end

theorem le_add_left {a b} (c : α): a ≤ b → c + a ≤ c + b :=
begin
  repeat {rw add_comm c},
  from le_add_right _,
end

theorem le_add_cancel_left: a ≤ b ↔ c + a ≤ c + b :=
begin
  repeat {rw add_comm c},
  rw le_add_cancel_right,
end

theorem le_neg_switch {a b : α}: a ≤ b → -b ≤ -a :=
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
  apply iff.intro le_neg_switch,
  assume hba,
  rw ←neg_neg a,
  rw ←neg_neg b,
  from le_neg_switch hba,
end

theorem zero_le_neg_switch_iff: 0 ≤ a ↔ -a ≤ 0 :=
begin
  conv {
    to_rhs,
    rw ←neg_zero,
  },
  rw le_neg_switch_iff,
end

theorem le_zero_neg_switch_iff: a ≤ 0 ↔ 0 ≤ -a :=
begin
  conv {
    to_rhs,
    rw ←neg_zero,
  },
  rw le_neg_switch_iff,
end

theorem le_neg_switch_neg: a ≤ -b ↔ b ≤ -a :=
begin
  conv {
    to_rhs,
    rw ←neg_neg b,
  },
  rw le_neg_switch_iff,
end

theorem square_nonneg: 0 ≤ a * a :=
begin
  cases le_total_order 0 a with ha ha, {
    from zero_le_mul ha ha,
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
(hsymm: ∀ a b: α, p a b → p b a) : (∀ a b: α, a ≤ b → p a b) → (∀ a b: α, p a b) :=
begin
  assume hwlog,
  intros a b,
  cases le_total_order a b with hmn hnm, {
    from hwlog a b hmn,
  }, {
    from hsymm _ _ (hwlog b a hnm),
  },
end

theorem le_iff_diff_nonneg: a ≤ b ↔ 0 ≤ b - a :=
begin
  have := le_add_cancel_right a b (-a),
  rw add_neg at this,
  from this,
end

theorem le_add_comb: a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
  assume hab hcd,
  transitivity (a + d), {
    from le_add_left _ hcd,
  }, {
    from le_add_right _ hab,
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
(hx : 0 ≤ a) (hz : 0 ≤ c) (hxy : a ≤ b) (hzw : c ≤ d):  a * c ≤ b * d :=
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

-- < THEOREMS

def lt : α → α → Prop := λ a b, ¬(b ≤ a)
instance: has_lt α := ⟨lt⟩

-- probably not needed with `change` etc
theorem lt_iff_nle: a < b ↔ ¬b ≤ a := iff.rfl

theorem lt_impl_ne {a b : α}: a < b → a ≠ b :=
begin
  assume hxy hxeqy,
  subst hxeqy,
  apply hxy,
  refl,
end

theorem lt_nrefl: ¬(a < a) :=
begin
  assume h,
  from lt_impl_ne h rfl,
end

theorem lt_impl_le {a b : α}: a < b → a ≤ b :=
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
theorem lt_very_antisymm_impl {a b : α}: a < b → ¬(b < a) :=
begin
  assume hab hba,
  apply lt_very_antisymmetric a b,
  split; assumption,
end

theorem lt_neg_switch_iff: a < b ↔ -b < -a :=
iff_to_contrapositive (le_neg_switch_iff b a)

theorem zero_lt_neg_switch_iff: 0 < a ↔ -a < 0 :=
begin
  conv {
    to_rhs,
    rw ←neg_zero,
  },
  from lt_neg_switch_iff _ _,
end

theorem lt_zero_neg_switch_iff: a < 0 ↔ 0 < -a :=
begin
  conv {
    to_rhs,
    rw ←neg_zero,
  },
  from lt_neg_switch_iff _ _,
end

theorem lt_neg_switch_neg {a b : α}: a < -b ↔ b < -a :=
begin
  conv {
    to_rhs,
    rw ←neg_neg b,
  },
  from lt_neg_switch_iff _ _,
end

@[trans]
theorem lt_trans {a} (b : α) {c}: a < b → b < c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ (lt_impl_le hab) (lt_impl_le hbc),
  have h := le_antisymm hac this,
  subst h,
  from lt_very_antisymmetric _ _ ⟨hbc, hab⟩,
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

theorem lt_comb {a b c d: α}: a < b → c < d → a + c < b + d :=
begin
  assume hab hcd,
  transitivity a + d,
  rw ←lt_add_cancel_left,
  assumption,
  rw ←lt_add_cancel_right,
  assumption,
end

theorem lt_le_chain {a} (b : α) {c}: a < b → b ≤ c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ (lt_impl_le hab) hbc,
  have h := le_antisymm this hac,
  subst h,
  clear hac this,
  have := le_antisymm (lt_impl_le hab) hbc,
  subst this,
  from lt_nrefl _ hab,
end

theorem le_lt_chain {a : α} (b : α) {c : α}: a ≤ b → b < c → a < c :=
begin
  assume hab hbc hac,
  have := le_trans _ hab (lt_impl_le hbc),
  have h := le_antisymm this hac,
  subst h,
  clear hac this,
  have := le_antisymm (lt_impl_le hbc) hab,
  subst this,
  from lt_nrefl _ hbc,
end

theorem lt_le_comb {a b c d: α}: a < b → c ≤ d → a + c < b + d :=
begin
  assume hab hcd,
  apply le_lt_chain (a + d),
  rw ←le_add_cancel_left,
  assumption,
  rw ←lt_add_cancel_right,
  assumption,
end

theorem le_lt_comb {a b c d: α}: a ≤ b → c < d → a + c < b + d :=
begin
  assume hab hcd,
  rw [add_comm, add_comm b],
  apply lt_le_comb; assumption,
end

-- worth a different type class?
-- condition is necessary since = makes
-- the trivial ring into an ordered ring
theorem nontrivial_zero_lt_one: (0: α) ≠ 1 → (0: α) < 1 :=
begin
  assume nontrivial h,
  from nontrivial (le_antisymm zero_le_one h),
end

theorem nontrivial_zero_lt_two: (0: α) ≠ 1 → (0: α) < 2 :=
begin
  assume nontrivial,
  change (0: α) < 1 + 1,
  rw ←add_zero (0: α),
  apply lt_comb; from nontrivial_zero_lt_one nontrivial,
end

-- Water
theorem nontrivial_zero_ne_two : (0 : α) ≠ 1 → (0 : α) ≠ 2 :=
begin
  assume nontrivial,
  apply lt_impl_ne,
  apply nontrivial_zero_lt_two,
  assumption,
end

-- Doesn't need ordering
theorem nontrivial_one_ne_two : (0 : α) ≠ 1 → (1 : α) ≠ 2 :=
begin
  sorry,
end

-- can't figure out hot to make decidability a typeclass thing
-- if we do a separate typeclass for decidably ordered rings
-- eg so we can do max/abs, move this there
theorem le_iff_lt_or_eq : a ≤ b ↔ a < b ∨ a = b :=
begin
  split, {
    assume hxy,
    by_cases h: b ≤ a, {
      right,
      from  le_antisymm hxy h,
    }, {
      left,
      assumption,
    },
  }, {
    assume h,
    cases h with h1 h2, {
      from lt_impl_le h1,
    }, {
      rw h2,
    },
  },
end

theorem lt_trichotomy : a = b ∨ a < b ∨ b < a :=
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
theorem lt_iff_le_and_neq : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  split, {
    assume h,
    split, {
      from lt_impl_le h,
    }, {
      from lt_impl_ne h,
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

theorem le_iff_lt_impl_lt : a ≤ b ↔ ∀ c, b < c → a < c :=
begin
  split; assume h, {
    intros c hbc,
    apply le_lt_chain b; assumption,
  }, {
    by_contradiction hba,
    change b < a at hba,
    apply lt_nrefl a,
    apply h a hba,
  },
end

theorem le_iff_le_impl_le : a ≤ b ↔ ∀ c, b ≤ c → a ≤ c :=
begin
  split; assume h, {
    intros c hbc,
    transitivity b; assumption,
  }, {
    by_contradiction hab,
    apply hab,
    apply h b,
    refl,
  },
end

section abs_max

def max (a b: α): α :=
if a ≤ b then b else a

def min (a b: α): α :=
if a ≤ b then a else b

def abs (a: α) :=
max a (-a)

instance decidable_lt : ∀ a b: α, decidable (a < b) :=
λ a b, not.decidable

def sign
(a: α): α :=
if 0 < a then 1
  else if a < 0 then -1
    else 0

@[simp]
theorem max_self : max a a = a :=
by apply if_pos; refl

theorem le_impl_max_right
(hmn: a ≤ b): max a b = b :=
begin
  unfold max,
  rw if_pos hmn,
end

theorem le_impl_max_left
(hnm: b ≤ a): max a b = a :=
begin
  by_cases a ≤ b, {
    rw [le_antisymm h hnm, max_self],
  }, {
    unfold max,
    rw if_neg h,
  },
end

theorem lt_impl_max_right
(hmn: a < b): max a b = b :=
le_impl_max_right _ _ (lt_impl_le hmn)

theorem lt_impl_max_left
(hnm: b < a): max a b = a :=
le_impl_max_left _ _ (lt_impl_le hnm)

theorem le_iff_max : a ≤ b ↔ max a b = b :=
begin
  split; assume h, {
    from le_impl_max_right _ _ h,
  }, {
    by_cases hmn : a ≤ b,
      assumption,
    rw ←lt_iff_nle at hmn,
    rw lt_impl_max_left _ _ hmn at h,
    exfalso,
    from lt_impl_ne hmn h.symm,
  },
end

theorem max_comm : max a b = max b a :=
begin
  by_cases a ≤ b,
    rw [le_impl_max_right _ _ h, le_impl_max_left _ _ h],
  rw ←lt_iff_nle at h,
  rw [lt_impl_max_right _ _ h, lt_impl_max_left _ _ h],
end

theorem le_iff_max_reverse : b ≤ a ↔ max a b = a :=
begin
  rw max_comm,
  from le_iff_max _ _,
end

theorem le_max_right : b ≤ max a b :=
begin
  by_cases b ≤ a,
    have := (le_iff_max _ _).mp h,
    rw max_comm at this,
    rwa this,
  rw ←lt_iff_nle at h,
  rw lt_impl_max_right _ _ h,
end

theorem le_max_left : a ≤ max a b :=
by rw max_comm; from le_max_right _ _

instance : is_commutative α max := ⟨λ a b, max_comm _ _⟩

-- Max distributes over itself
theorem max_max : max a (max b c) = max (max a b) (max a c) :=
begin
  unfold max,
  by_cases hmmxnk: a ≤ (max b c); unfold max at hmmxnk, {
    rw if_pos hmmxnk,
    by_cases hnk: b ≤ c, {
      rw if_pos hnk,
      rw if_pos hnk at hmmxnk,
      repeat {rw if_pos hmmxnk},
      by_cases hmn: a ≤ b, {
        repeat {rw if_pos hmn},
        rw if_pos hnk,
      }, {
        repeat {rw if_neg hmn},
        rw if_pos hmmxnk,
      },
    }, {
      rw if_neg hnk,
      rw if_neg hnk at hmmxnk,
      repeat {rw if_pos hmmxnk},
      by_cases hmk: a ≤ c, {
        repeat {rw if_pos hmk},
        rw if_neg hnk,
      }, {
        repeat {rw if_neg hmk},
        have := max_comm,
        unfold max at this,
        rw this,
        rw if_pos hmmxnk,
      },
    },
  }, {
    rw if_neg hmmxnk,
    have hmk: ¬a ≤ c, {
      assume hmk,
      have := le_trans _ hmk (le_max_right b c),
      from hmmxnk this,
    },
    have hmn: ¬a ≤ b, {
      assume hmk,
      have := le_trans _ hmk (le_max_left b c),
      from hmmxnk this,
    },
    repeat {rw if_neg hmk <|> rw if_neg hmn},
    rw if_pos (le_refl a),
  },
end

theorem max_eq_either : max a b = a ∨ max a b = b :=
begin
  by_cases a ≤ b,
    right, rwa le_impl_max_right,
  left,
  rw ←lt_iff_nle at h,
  rwa lt_impl_max_left,
end

theorem max_assoc : max (max a b) c = max a (max b c) :=
begin
  by_cases a ≤ b, {
    rw le_impl_max_right _ _ h,
    have : a ≤ max b c,
      transitivity b,
        assumption,
      from le_max_left _ _,
    rw le_impl_max_right _ _ this,
  }, {
    rw ←lt_iff_nle at h,
    rw max_comm a b,
    rw le_impl_max_right _ _ (lt_impl_le h),
    by_cases h': a ≤ c, {
      rw le_impl_max_right _ _ h',
      have := le_trans _ (lt_impl_le h) h',
      rw le_impl_max_right _ _ this,
      rw le_impl_max_right _ _ h',
    }, {
      rw ←lt_iff_nle at h',
      rw max_comm a c,
      rw le_impl_max_right _ _ (lt_impl_le h'),
      cases max_eq_either b c with h h; rw h; clear h,
      rw max_comm a b,
      rw le_impl_max_right _ _ (lt_impl_le h),
      rw max_comm a c,
      rw le_impl_max_right _ _ (lt_impl_le h'),
    },
  },
end

instance : is_associative α max := ⟨λ a b c, max_assoc _ _ _⟩

theorem max_sum_le : max (a + c) (b + d) ≤ max a b + max c d :=
begin
  cases max_eq_either (a + c) (b + d) with h; rw h; clear h, {
    from le_add_comb _ _ _ _ (le_max_left _  _) (le_max_left _ _),
  }, {
    from le_add_comb _ _ _ _ (le_max_right _  _) (le_max_right _ _),
  },
end

-- yes it takes longer this way abut it's a matter of principle
theorem nonneg_mul_max : 0 ≤ a → a * max b c = max (a * b) (a * c) :=
begin
  assume h0m,
  revert b c,
  apply wlogle, {
    intros b c,
    assume h,
    rw max_comm c b,
    rw max_comm (a * c) (a * b),
    assumption,
  }, {
    intros b c,
    assume hnk,
    rw le_impl_max_right _ _ hnk,
    rw le_impl_max_right _ _ (le_mul_nonneg_left _ _ _ h0m hnk),
  },
end

theorem abs_neg : abs (-b) = abs b :=
begin
  unfold abs,
  rw neg_neg,
  from max_comm _ _,
end

-- Rename to abs_sub?
theorem abs_sub_switch : abs (a - b) = abs (b - a) :=
by rw [sub_def, ←abs_neg, neg_distr, neg_neg, add_comm, ←sub_def]

theorem abs_of_nonneg (h : 0 ≤ a): abs a = a :=
begin
  unfold abs,
  rw max_comm,
  rw ←le_iff_max,
  transitivity (0: α), {
    rw le_neg_switch_iff,
    rw neg_zero,
    rw neg_neg,
    assumption,
  }, {
    assumption,
  },
end

theorem abs_one : abs (1 : α) = 1 :=
begin
  apply abs_of_nonneg,
  exact zero_le_one,
end

theorem abs_of_pos : 0 < a → abs a = a :=
begin
  assume h,
  apply abs_of_nonneg,
  apply lt_impl_le,
  assumption,
end

theorem abs_of_neg : a < 0 → abs a = -a :=
begin
  assume ha0,
  rw ←abs_neg,
  rw lt_neg_switch_iff at ha0,
  rw neg_zero at ha0,
  rw abs_of_pos _ ha0,
end

theorem abs_of_nonpos : a ≤ 0 → abs a = -a :=
begin
  assume ha0,
  rw ←abs_neg,
  rw le_neg_switch_iff at ha0,
  rw neg_zero at ha0,
  rw abs_of_nonneg _ ha0,
end

theorem abs_nonneg : 0 ≤ abs a :=
begin
  by_cases h0a: 0 ≤ a, {
    rw abs_of_nonneg _ h0a,
    assumption,
  }, {
    rw ←abs_neg,
    change a < 0 at h0a,
    rw lt_neg_switch_iff at h0a,
    rw neg_zero at h0a,
    rw abs_of_pos _ h0a,
    apply lt_impl_le, assumption,
  },
end

private theorem abs_cancel_abs_mul_within: abs (abs a * b) = abs (a * b) :=
begin
  unfold abs,
  by_cases h: -a ≤ a,
    rw le_impl_max_left _ _ h,
  rw ←lt_iff_nle at h,
  rw [lt_impl_max_right _ _ h, max_comm, neg_mul, neg_neg],
end

-- Short lemma above avoids any casework
theorem abs_mul : abs (a * b) = abs a * abs b :=
begin
  have: abs a * abs b = abs (abs a * abs b),
    have : 0 ≤ abs a * abs b,
      rw ←zero_mul (0: α),
      apply le_mul_comb_nonneg, any_goals { refl },
        from abs_nonneg _,
        from abs_nonneg _,
      rw abs_of_nonneg _ this,
  rw this,
  rw [abs_cancel_abs_mul_within, mul_comm a (abs b), abs_cancel_abs_mul_within, mul_comm],
end

-- The following three theorems are practically equivalent, needs reorganising a bit
theorem abs_nonneg_mul : 0 ≤ a → ∀ b, a * abs b = abs (a * b) :=
begin
  assume h0m,
  intro b,
  conv {
    to_lhs,
    congr,
    rw ←abs_of_nonneg _ h0m,
  },
  rw abs_mul,
end

-- le_sqrt_nonneg?
-- theorem abs_le_square : -- abs a ≤ abs b ↔ a * a ≤ b * b :=
-- begin
--   split; assume h, {
--     have := le_mul_comb_nonneg _ _ _ _ (abs_nonneg _) (abs_nonneg _) h h,
--     rw [←abs_mul, ←abs_mul] at this,
--     rwa [abs_of_nonneg _ (square_nonneg a), abs_of_nonneg _ (square_nonneg b)] at this,
--   }, {
--     rw [←abs_of_nonneg _ (square_nonneg a), ←abs_of_nonneg _ (square_nonneg b)] at h,
--     rwa [abs_mul, abs_mul, ←le_sqrt_nonneg (abs_nonneg _) (abs_nonneg _)] at h,
--   },
-- end

theorem self_le_abs : a ≤ abs a := le_max_left _ _

theorem triangle_ineq : abs (a + b) ≤ abs a + abs b :=
begin
  unfold abs,
  rw neg_distr,
  from max_sum_le _ _ _ _,
end

theorem neg_max : -max a b = max (-a) (-b) :=
begin
  sorry,
end

theorem abs_abs : abs (abs a) = abs a :=
begin
  unfold abs,
  rw [max_comm, neg_max, neg_neg, max_comm (-a), max_self],
end

theorem triangle_ineq_sub : abs (abs a - abs b) ≤ abs (a - b) :=
begin
  sorry,
end

theorem abs_eq_plusminus : abs a = a ∨ abs a = -a := max_eq_either a (-a)

theorem abs_zero : abs (0: α) = 0 :=
begin
  cases abs_eq_plusminus (0: α) with h h, {
    assumption,
  }, {
    rw h,
    rw neg_zero,
  },
end

-- I renamed this because it's so handy to have `abs` at the front to help find it
theorem abs_zero_iff_zero : abs a = 0 ↔ a = 0 :=
begin
  split, tactic.swap, {
    assume hm0,
    rw hm0,
    rw abs_zero,
  }, {
    assume habs,
    unfold abs at habs,
    unfold max at habs,
    by_cases hmm: (a ≤ -a), {
      rw if_pos hmm at habs,
      apply add_cancel_right _ _ (-a),
      rw add_neg,
      rw zero_add,
      rw habs,
    }, {
      rw if_neg hmm at habs,
      assumption,
    },
  },
end

theorem sign_of_pos: 0 < a → sign a = 1 :=
begin
  assume h0a,
  unfold sign,
  rw if_pos h0a,
end

theorem sign_of_neg : a < 0 → sign a = -1 :=
begin
  assume ha0,
  unfold sign,
  rw if_neg (lt_very_antisymm_impl ha0),
  rw if_pos ha0,
end

theorem sign_zero : sign (0: α) = 0 :=
begin
  unfold sign,
  rw if_neg (lt_nrefl _),
  rw if_neg (lt_nrefl _),
end

theorem sign_mul_self_abs : a * sign a = abs a :=
begin
  by_cases h0m: 0 < a, {
    rw sign_of_pos _ h0m,
    rw mul_one,
    rw abs_of_pos _ h0m,
  }, {
    by_cases hm0: a < 0, {
      rw sign_of_neg _ hm0,
      rw mul_neg,
      rw mul_one,
      rw lt_add_cancel_right _ _ (-a) at hm0,
      rw add_neg at hm0,
      rw zero_add at hm0,
      rw ←abs_neg,
      rw abs_of_pos _ hm0,
    }, {
      cases lt_trichotomy 0 a, {
        rw ←h,
        rw zero_mul,
        rw abs_zero,
      }, {
        cases h; contradiction,
      },
    },
  },
end

theorem sign_zero_iff_zero : sign a = 0 ↔ a = 0 :=
begin
  split, {
    assume hsgnm,
    rw ←abs_zero_iff_zero,
    rw ←sign_mul_self_abs,
    rw hsgnm,
    rw mul_zero,
  }, {
    assume h, rw h,
    rw sign_zero,
  },
end

theorem sign_abs_mul : sign a * abs a = a :=
begin
  by_cases ha: 0 < a, {
    rw sign_of_pos _ ha,
    rw abs_of_pos _ ha,
    rw one_mul,
  }, {
    change ¬¬a ≤ 0 at ha,
    rw decidable.not_not_iff at ha,
    rw abs_of_nonpos _ ha,
    by_cases ha': a < 0, {
      rw sign_of_neg _ ha',
      rw neg_mul_neg,
      rw one_mul,
    }, {
      change ¬¬0 ≤ a at ha',
      rw decidable.not_not_iff at ha',
      have ha0 := le_antisymm ha ha',
      rw ha0,
      rw sign_zero,
      rw zero_mul,
    },
  },
end

theorem sign_neg : sign (-a) = -sign a :=
begin
  by_cases h0a: 0 < a, {
    rw sign_of_pos _ h0a,
    rw zero_lt_neg_switch_iff at h0a,
    rw sign_of_neg _ h0a,
  }, {
    unfold sign,
    rw if_neg h0a,
    rw zero_lt_neg_switch_iff at h0a,
    rw if_neg h0a,
    by_cases ha0: a < 0, {
      rw if_pos ha0,
      rw lt_zero_neg_switch_iff at ha0,
      rw if_pos ha0,
      rw neg_neg,
    }, {
      rw if_neg ha0,
      rw lt_zero_neg_switch_iff at ha0,
      rw if_neg ha0,
      rw neg_zero,
    },
  },
end

theorem zero_le_self_mul_sign : 0 ≤ a * sign a :=
begin
  rw sign_mul_self_abs,
  from abs_nonneg _,
end

theorem zero_lt_self_mul_sign : a ≠ 0 → 0 < a * sign a :=
begin
  assume han0,
  unfold sign,
  by_cases h0a: 0 < a, {
    rw if_pos h0a,
    rw mul_one,
    assumption,
  }, {
    rw if_neg h0a,
    by_cases ha0: a < 0, {
      rw if_pos ha0,
      rw mul_neg,
      rw mul_one,
      rw lt_neg_switch_iff,
      rw neg_neg,
      rw neg_zero,
      assumption,
    }, {
      exfalso,
      apply han0,
      apply le_antisymm, {
        from decidable.of_not_not h0a,
      }, {
        from decidable.of_not_not ha0,
      },
    },
  },
end

theorem zero_lt_sign_mul_self : a ≠ 0 → 0 < sign a * a :=
begin
  assume han0,
  rw mul_comm,
  apply zero_lt_self_mul_sign,
  assumption,
end

theorem abs_lt_iff_lt_both : abs a < b ↔ -b < a ∧ a < b :=
begin
  split; assume h, {
    split, {
      rw lt_neg_switch_iff,
      rw neg_neg,
      apply le_lt_chain (abs a), {
        rw ←abs_neg,
        from self_le_abs _,
      }, {
        assumption,
      },
    }, {
      apply le_lt_chain (abs a), {
        from self_le_abs _,
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

theorem abs_lt_left : abs a < b → -b < a :=
λ h, by rw abs_lt_iff_lt_both at h; from h.left

theorem abs_lt_right : abs a < b → a < b :=
λ h, by rw abs_lt_iff_lt_both at h; from h.right

theorem lt_abs_impl_lt_either : a < abs b → b < -a ∨ a < b :=
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

theorem abs_diff_lt_left : abs (a - b) < c → b - c < a :=
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

theorem abs_diff_lt_right :abs (a - b) < c → a < b + c :=
begin
  assume h,
  rw lt_neg_switch_iff,
  rw ←abs_neg at h,
  change abs (-(a + -b)) < c at h,
  rw neg_distr at h,
  rw neg_distr,
  from abs_diff_lt_left _ _ _ h,
end

open mynat

-- Should be somewhere else
def max_upto : mynat → (mynat → α) → α
| 0        f := f 0
| (succ M) f := max (f (succ M)) (max_upto M f)

theorem max_upto_ge_before {N n : mynat} (hnN : n ≤ N) (f  : mynat → α): f n ≤ max_upto N f :=
begin
  induction N with N hN,
    dsimp at *,
    have hn := mynat.le_zero hnN,
    subst hn,
    refl,
  change _ ≤ max (f (succ N)) (max_upto N f),
  rw mynat.le_iff_lt_or_eq at hnN,
  cases hnN with hlt heq, {
    rw ←le_iff_lt_succ at hlt,
    transitivity max_upto N f,
      apply hN,
      assumption,
    apply le_max_right,
  }, {
    subst heq,
    apply le_max_left,
  },
end

end abs_max

end ordered_myring

end hidden
