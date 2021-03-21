import .basic

namespace hidden

-- nontriviality axiom?
class integral_domain (α : Type) extends myring α :=
(mul_integral_left (a b : α) : a ≠ 0 → b * a = 0 → b = 0) -- This form isn't that useful

namespace integral_domain

variables {α : Type} [integral_domain α]
variables (a b c : α)

theorem mul_integral_right : a ≠ 0 → a * b = 0 → b = 0 :=
begin
  assume ha h,
  apply mul_integral_left a _,
    assumption,
  rwa myring.mul_comm,
end

-- This requires decidability
theorem mul_integral [decidable (a = 0)] : a * b = 0 → a = 0 ∨ b = 0 :=
begin
  assume hab,
  by_cases a = 0,
    left, assumption,
  right,
  apply mul_integral_right a; assumption,
end

theorem mul_nzero {a b : α}: a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
  intros ha hb hab,
  apply ha,
  apply mul_integral_left b; assumption,
end

theorem mul_cancel_right : b ≠ 0 → a * b = c * b → a = c :=
begin
  assume hb h,
  rw ←myring.sub_to_zero_iff_eq at ⊢ h,
  rw ←myring.sub_mul at h,
  apply mul_integral_left b _ hb h,
end

theorem mul_cancel_left : a ≠ 0 → a * b = a * c → b = c :=
begin
  assume ha h,
  apply mul_cancel_right _ a _,
    assumption,
  rwa [myring.mul_comm a, myring.mul_comm a] at h,
end

end integral_domain

end hidden
