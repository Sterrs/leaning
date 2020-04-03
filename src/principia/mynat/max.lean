import .nat_sub

namespace hidden

open mynat
-- TODO: generalise this to relevant types and relations
def max (a b : mynat) : mynat :=
if a ≤ b then b else a
def min (a b : mynat) : mynat :=
if a ≤ b then b else a

variables {a b c : mynat}

theorem le_imp_max2 (h : a ≤ b) : max a b = b :=
begin
  unfold max,

end
theorem le_imp_max1 (h : a ≤ b) : max b a = b :=
begin
  sorry
end

@[simp]
theorem max_same : max a a = a := le_imp_max2 le_refl
@[simp]
theorem max_zero : max 0 a = a := le_imp_max2 zero_le
@[simp]
theorem max_succ : max a (succ a) = succ a := le_imp_max2 le_succ

theorem max_comm : max a b = max b a :=
by cases le_total_order a b; rw [le_imp_max1 h, le_imp_max2 h]

theorem max_le : a ≤ max a b :=
begin
  cases le_total_order a b,
    rwa le_imp_max2 h,
  rw [max_comm, le_imp_max2 h],
  from le_refl,
end

theorem max_assoc : max a (max b c) = max (max a b) c :=
begin
  sorry
end

end hidden
