import naturals.le

namespace hidden

open mynat

def lt (m n: mynat) := ¬n ≤ m
instance: has_lt mynat := ⟨lt⟩

-- Given a proposition, we can say that ifthere are arbitrarily large mynat
-- satisfying it, then there are infinitely many satisfying it.
def infinitely_many (statement : mynat → Prop) : Prop :=
∀ n : mynat, ∃ m : mynat, n < m ∧ statement m

variables m n p k : mynat

theorem lt_succ_cancel: succ m < succ n → m < n :=
begin
  assume hsmsn hmn,
  apply hsmsn,
  have h := le_add n m 1 hmn,
  simp at h,
  cc,
end

theorem lt_cancel: m + k < n + k → m < n :=
begin
  assume hmknk hmn,
  apply hmknk,
  from le_add _ _ _ hmn,
end

theorem lt_cancel_strong: m + k < n → m < n :=
begin
  assume hmkn hmn,
  apply hmkn,
  apply le_add_rhs,
  cc,
end

theorem lt_add_rhs: m < n → m < n + k :=
begin
  assume hmn hmnk,
  apply hmn,
  apply le_cancel_strong _ _ k,
  cc,
end

theorem zero_lt: m ≠ 0 → 0 < m :=
begin
  assume hmnz hmlz,
  from hmnz (le_zero _ hmlz),
end

theorem lt_to_add_succ: m < m + succ n :=
begin
  assume hmmsn,
  cases hmmsn with d hd,
  rw [←add_zero m, add_assoc m _ _, add_assoc m _ _] at hd,
  have hd' := add_cancel _ _ _ hd,
  simp at hd',
  from succ_ne_zero _ (eq.symm hd'),
end

-- this is far too long
theorem lt_comb (a b c d: mynat): a < b → c < d → a + c < b + d :=
begin
  assume hab hcd,
  assume hbdac,
  cases (le_total_order a b),
  cases (le_total_order c d),
  have hacbd := le_comb a b c d h h_1,
  have hacebd := le_antisymm _ _ hacbd hbdac,
  cases h with x hx,
  cases h_1 with y hy,
  rw [hx, hy, add_assoc] at hacebd,
  have hcxcy := add_cancel _ _ _ hacebd,
  rw [add_comm, add_assoc, ←add_zero c] at hcxcy,
  have hxy := add_cancel _ _ _ hcxcy,
  have hy0 := add_integral _ _ (eq.symm hxy),
  rw hy0 at hy,
  rw [hy, add_zero] at hcd,
  from hcd (le_refl c),
  from hcd h_1,
  from hab h,
end

theorem lt_nzero: ¬m < 0 :=
begin
  assume mlz,
  from mlz (zero_le m),
end

theorem lt_add: m < n → m + k < n + k :=
begin
  assume hmn hmknk,
  from hmn (le_cancel _ _ _ hmknk),
end

theorem lt_nrefl: ¬m < m :=
begin
  assume hmm,
  from hmm (le_refl m),
end

theorem lt_impl_le: m < n → m ≤ n :=
begin
  assume hmn,
  cases (le_total_order m n) with hmltn hnm,
  from hmltn,
  exfalso, from hmn hnm,
end

theorem le_iff_lt_succ: m ≤ n ↔ m < succ n :=
begin
  split,
  assume hmn,
  cases hmn with d hd,
  rw hd,
  assume hmsd,
  cases hmsd with d' hd',
  rw [succ_add, add_assoc, ←add_succ, ←add_zero m, add_assoc] at hd',
  have hzsucc := add_cancel _ _ _ hd',
  rw zero_add at hzsucc,
  from succ_ne_zero _ (eq.symm hzsucc),
  assume hmsn,
  -- this total ordering theorem is crazy powerful. It feels like you need
  -- classical logic until you remember it exists
  cases (le_total_order m n) with hmn hnm,
  from hmn,
  cases hnm with d hd,
  cases d,
  rw [hd, zz, add_zero],
  from le_refl n,
  have hsnm: succ n ≤ m,
  existsi d,
  rw [hd, add_succ, succ_add],
  exfalso, from hmsn hsnm,
end

-- somehow this feels like it's not using le_iff_lt_succ enough
theorem le_iff_lt_or_eq: m ≤ n ↔ m < n ∨ m = n :=
begin
  split,
  assume hmn,
  cases hmn with d hd,
  cases d,
  simp at hd,
  right, rw hd,
  left,
  rw hd,
  from lt_to_add_succ _ _ ,
  assume hmnmn,
  cases hmnmn,
  from lt_impl_le _ _ hmnmn,
  rw hmnmn,
  from le_refl n,
end

-- it seems that inductive types give all sorts of classical-feeling results
-- without any of the excluded middle
theorem lt_dne: ¬m < n → n ≤ m :=
begin
  assume hnmn,
  cases (le_total_order m n),
  cases h with d hd,
  cases d,
  simp at hd,
  rw hd,
  from le_refl m,
  have hmln: m < n,
  rw hd,
  from lt_to_add_succ _ _,
  exfalso, from hnmn hmln,
  from h,
end

theorem lt_strict: ¬(m < n ∧ n < m) :=
begin
  assume hmnnm,
  cases hmnnm,
  from hmnnm_left (lt_impl_le _ _ hmnnm_right),
end

theorem lt_strict_order: m = n ∨ m < n ∨ n < m :=
begin
  cases (le_total_order m n),
  rw le_iff_lt_or_eq _ _ at h,
  cases h,
  cc,
  cc,
  rw le_iff_lt_or_eq _ _ at h,
  cases h,
  cc,
  cc,
end

theorem lt_trans: m < n → n < k → m < k :=
begin
  assume hmn hnk hkm,
  cases hkm with d hd,
  cases d,
  simp at hd,
  rw hd at hmn,
  from lt_strict _ _ (and.intro hnk hmn),
  rw hd at hmn,
  have hkln: k ≤ n
  := le_cancel_strong _ _ (succ d) (lt_impl_le _ _ hmn),
  from hnk hkln,
end

end hidden
