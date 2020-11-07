namespace hidden

class mygroup (α : Type)
extends has_mul α, has_inv α :=
(e : α)
(mul_assoc (a b c : α) : a * b * c = a * (b * c))
(mul_id (a : α) : a * e = a)
(mul_inv (a : α) : a * a⁻¹ = e)

namespace mygroup

variables {α : Type} [mygroup α]

variables {a b c : α}
-- This sucks

theorem mul_by_right : a = b → a * c = b * c :=
begin
  assume h,
  congr,
  assumption,
end

theorem mul_cancel_right (c : α) : a * c = b * c → a = b :=
begin
  assume h,
  have := congr_arg (λ d, d * c⁻¹) h,
  dsimp only [] at this,
  repeat { rwa [mul_assoc, mul_inv, mul_id] at this },
end

theorem mul_right (c : α) : a = b ↔ a * c = b * c :=
⟨mul_by_right, mul_cancel_right c⟩

theorem mul_by_left : a = b → c * a = c * b :=
begin
  assume h,
  congr,
  assumption,
end

theorem inv_mul : a⁻¹ * a = e :=
begin
  -- This is actually a really hard theorem
  rw [←mul_inv a⁻¹, ←mul_id (a⁻¹ * a), ←mul_inv a⁻¹, ←mul_assoc],
  apply mul_by_right,
  rw [mul_assoc, mul_inv, mul_id],
end

theorem id_mul (a : α) : e * a = a :=
by rw [←mul_inv a, mul_assoc, inv_mul, mul_id]

theorem mul_cancel_left : c * a = c * b → a = b :=
begin
  assume h,
  have := congr_arg (λ d, c⁻¹ * d) h,
  dsimp only [] at this,
  repeat { rwa [←mul_assoc, inv_mul, id_mul] at this },
end

theorem mul_left (c : α) : a = b ↔ c * a = c * b :=
⟨mul_by_left, mul_cancel_left⟩

theorem id_unique : a * b = a ↔ b = e :=
begin
  split; assume h,
    rwa [mul_left a, mul_id],
  subst h,
  from mul_id a,
end

theorem inv_unique : a * b = e ↔ b = a⁻¹ :=
begin
  split; assume h,
    rwa [mul_left a, mul_inv],
  subst h,
  from mul_inv a,
end

end mygroup

end hidden
