import ..myset.basic
import .prime
import ..quotint.dvd
import ..logic

/- Noncomputable HCF

In this file we make no attempt to remain computable or
minimise the axioms used.

We construct the HCF of a and b as the smallest positive
integer h for which there exist integers x and y such
that a * x + b * y = h, and then go on to prove some
properties of this.
-/

namespace hidden

open quotint

namespace mynat

/-- Non-zero linear combinations of naturals -/
def lin_combs (a b : mynat) : myset mynat :=
λ c, c ≠ 0 ∧ ∃ x y : quotint, ↑a * x + ↑b * y = ↑c

theorem lin_combs_comm (a b : mynat) : lin_combs a b = lin_combs b a :=
begin
  apply funext,
  intro c,
  apply propext,
  split,
  all_goals {
    assume h,
    unfold lin_combs at *,
    split,
      from h.left,
    cases h.right with x hx,
    cases hx with y hxy,
    existsi y,
    existsi x,
    rwa quotint.add_comm,
  },
end

theorem lin_combs_nemp {a b : mynat} : a ≠ 0 ∨ b ≠ 0 → ¬myset.empty (lin_combs a b) :=
begin
  assume hab,
  rw ←myset.exists_iff_nempty,
  cases hab with ha hb, {
    existsi a,
    split,
      assumption,
    existsi (1 : quotint),
    existsi (0 : quotint),
    rw [quotint.mul_one, quotint.mul_zero, quotint.add_zero],
  }, {
    existsi b,
    split,
      assumption,
    existsi (0 : quotint),
    existsi (1 : quotint),
    rw [quotint.mul_one, quotint.mul_zero, quotint.zero_add],
  },
end

-- 0 if both 0, sadly this makes it an if :(
-- Inherits noncomputablility from `min`
/-- Given two integers, (noncomputably) get their hcf, and if both are
zero, return zero. -/
noncomputable def hcf (a b : mynat) : mynat :=
if h : a ≠ 0 ∨ b ≠ 0 then
  min (lin_combs a b) (lin_combs_nemp h)
else 0

variables m n k : mynat

theorem hcf_comm : hcf m n = hcf n m :=
begin
  by_cases m ≠ 0 ∨ n ≠ 0,
    unfold hcf,
    rw [dif_pos h, dif_pos (or.symm h)],
    apply min_rw,
    from lin_combs_comm m n,
  unfold hcf,
  have : ¬(n ≠ 0 ∨ m ≠ 0),
    assume hnm,
    from h (or.symm hnm),
  rw [dif_neg h, dif_neg this],
end

private lemma common_factor_dvd_lin_comb (k m n a : mynat):
k ∣ m → k ∣ n → a ∈ lin_combs m n → k ∣ a :=
begin
  assume hkm hkn h,
  cases h with ha h,
  cases h with x hx,
  cases hx with y hxy,
  have : ↑k ∣ ↑m * x + ↑n * y,
    apply quotint.dvd_sum,
      apply quotint.dvd_mul,
      apply quotint.coe_coe_dvd.mp,
      assumption,
    apply quotint.dvd_mul,
    apply quotint.coe_coe_dvd.mp,
    assumption,
  apply quotint.coe_coe_dvd.mpr,
  rwa ←hxy,
end

theorem hcf_is_lin_comb {m n : mynat} (h : m ≠ 0 ∨ n ≠ 0):
hcf m n ∈ lin_combs m n :=
begin
  unfold hcf,
  rw dif_pos h,
  from min_property _,
end

theorem hcf_min_if_one_nzero {m n : mynat} (h : m ≠ 0 ∨ n ≠ 0) :
hcf m n = min (lin_combs m n) (lin_combs_nemp h) :=
begin
  unfold hcf,
  rw dif_pos h,
end

theorem common_factor_dvd_hcf {k m n : mynat} :
k ∣ m → k ∣ n → k ∣ hcf m n :=
begin
  by_cases m ≠ 0 ∨ n ≠ 0; assume hkm hkn,
    apply common_factor_dvd_lin_comb k m n (hcf m n),
    any_goals { assumption, },
    from hcf_is_lin_comb h,
  have : hcf m n = 0,
    unfold hcf,
    rw dif_neg h,
  rw this,
  from dvd_zero,
end

theorem hcf_zero_iff_both_zero : hcf m n = 0 ↔ ¬(m ≠ 0 ∨ n ≠ 0) :=
begin
  split; assume h, {
    assume hmn0,
    unfold hcf at h,
    rw dif_pos hmn0 at h,
    have := min_property (lin_combs_nemp hmn0),
    rw myset.mem_def at this,
    cases this with h0 hright,
    contradiction,
  }, {
    unfold hcf,
    rw dif_neg h,
  },
end

-- NOTE: This example breaks if you open classical. Why?
-- (see below)
example {m n : mynat} (h : m ≠ 0 ∨ n ≠ 0) :
hcf m n = min (lin_combs m n) (lin_combs_nemp h) :=
begin
  unfold hcf,
  rw dif_pos h,
end

-- Let's open classical and make all propositions decidable

open classical

-- Proving dvd decidable almost certainly requires well-founded recursion
local attribute [instance] prop_decidable

-- Brok
example {m n : mynat} (h : m ≠ 0 ∨ n ≠ 0) :
hcf m n = min (lin_combs m n) (lin_combs_nemp h) :=
begin
  unfold hcf,
  -- rw dif_pos h,
  sorry,
end

-- A ridiculous proof, at this point might as well just be constructive
-- We need dvd decidable
-- TODO: Move somewhere, I guess
/-- Off-brand division algorithm -/
theorem exists_remainder {k n : mynat} :
k ≠ 0 → ¬k ∣ n → ∃ m r, 0 ≠ r ∧ r < k ∧ k ∣ m ∧ n = m + r :=
begin
  assume hk,
  induction n with n hn,
    assume h,
    have : k ∣ zero,
      rw zz,
      from dvd_zero,
    contradiction,
  assume hsucc,
  by_cases hkn: k ∣ n, {
    existsi n,
    existsi (1 : mynat),
    split,
      apply mynat.no_confusion,
    split,
      assume hk1,
      cases le_one hk1,
        contradiction,
      have : k ∣ (succ n),
        rw h,
        from one_dvd,
      contradiction,
    split,
      assumption,
    refl,
  }, {
    cases hn hkn with m hm,
    cases hm with r hmr,
    cases hmr with h0r hmr,
    cases hmr with hrk hmr,
    cases hmr with hkm hnmr,
    existsi m,
    existsi (succ r),
    split,
      apply mynat.no_confusion,
    split,
      rw [lt_iff_succ_le, le_iff_lt_or_eq] at hrk,
      cases hrk,
        assumption,
      have := congr_arg succ hnmr,
      cases hkm with a ha,
      rw [←add_succ, hrk, ha] at this,
      conv at this {
        to_rhs, congr, skip,
        rw ←mynat.one_mul k, skip,
      },
      rw ←add_mul at this,
      have hcontra : k ∣ (succ n),
        existsi (a + 1),
        assumption,
      contradiction,
    split,
      assumption,
    rwa [add_succ, hnmr],
  },
end

theorem hcf_dvd_left (h : m ≠ 0 ∨ n ≠ 0): hcf m n ∣ m :=
begin
  by_contradiction hdvd,
  have hprop := min_property (lin_combs_nemp h),
  rw ←hcf_min_if_one_nzero h at hprop,
  cases hprop with h0 hprop,
  cases hprop with x hx,
  cases hx with y hxy,

  -- Again, unfold enormous string of ∧.
  -- Mathlib has `rcases` tactic which makes this pleasant.
  cases exists_remainder h0 hdvd with a ha,
  cases ha with r har,
  cases har with h0r har,
  cases har with hrhcf har,
  cases har with hhcfdvd hmxr,
  cases hhcfdvd with q hq,

  have hmul := congr_arg (λ x, ↑q * x) hxy,
  dsimp only [] at hmul,
  rw [coe_coe_mul, ←hq] at hmul,

  have hcoe := congr_arg (λ x, (↑x : quotint)) hmxr,
  dsimp only [] at hcoe,
  rw [←coe_coe_add, ←quotint.add_cancel (-↑r), quotint.add_assoc,
      self_neg_add, quotint.add_zero] at hcoe,

  rw [←hcoe, ←quotint.add_cancel (↑r), quotint.add_assoc, neg_self_add,
      quotint.add_zero, quotint.add_comm,
      ←quotint.add_cancel (-(↑q * (↑m * x + ↑n * y))), quotint.add_assoc,
      self_neg_add, quotint.add_zero, ←mul_neg_with, quotint.mul_add,
      ←quotint.mul_one (↑m)] at hmul,

  have : ↑m * 1 + (-↑q * (↑m * 1 * x) + -↑q * (↑n * y)) =
         ↑m * 1 + ↑m * (1 * -↑q * x) + ↑n * (-↑q * y),
    ac_refl,
  rw [this, ←quotint.mul_add] at hmul, clear this,

  suffices : r ∈ lin_combs m n,
    have hle := min_le (lin_combs_nemp h) this,
    rw ←hcf_min_if_one_nzero h at hle,
    contradiction,

  split,
    from h0r.symm,
  existsi (1 + 1 * -↑q * x),
  existsi (-↑q * y),
  symmetry,
  assumption,
end

theorem hcf_dvd_right (h : m ≠ 0 ∨ n ≠ 0): hcf m n ∣ n :=
by rw hcf_comm; from hcf_dvd_left n m (or.symm h)

theorem bezouts_lemma {m n k : mynat} (h : m ≠ 0 ∨ n ≠ 0) :
(∃ x y : quotint, ↑m * x + ↑n * y = k) ↔ hcf m n ∣ k :=
begin
  split; assume h₁, {
    cases h₁ with x hx,
    cases hx with y hxy,
    cases hcf_dvd_left _ _ h with a ha,
    cases hcf_dvd_right _ _ h with b hb,
    apply quotint.coe_coe_dvd.mpr,
    existsi (↑a * x + ↑b * y),
    rw [quotint.mul_comm, quotint.mul_add, ←quotint.mul_assoc, ←quotint.mul_assoc,
        coe_coe_mul, coe_coe_mul, mul_comm, mul_comm _ b, ←ha, ←hb],
    symmetry, assumption,
  }, {
    sorry,
  },
end

end mynat

end hidden
