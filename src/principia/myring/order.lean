import .basic

namespace hidden

class ordered_myring (α : Type) extends myring α, has_le α :=
(le_add_right (a b c : α) : a ≤ b → a + c ≤ b + c) -- hmm, normally this is ↔
(zero_le_mul (a b : α) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

namespace ordered_myring

variables {α : Type} [ordered_myring α] (a b c : α)



def lt : α → α → Prop := λ a b, ¬(b ≤ a)
instance: has_lt α := ⟨lt⟩

end ordered_myring

end hidden

-- -- Sign

-- def sign: myint → myint :=
-- quotient.lift (λ n, ⟦int_pair.sign n⟧) int_pair.sign_well_defined

-- theorem sign_eq_cls {x: int_pair.int_pair} {n: myint}:
-- n = ⟦x⟧ → sign n = ⟦int_pair.sign x⟧ :=
-- λ hnx, by rw hnx; refl

-- theorem sign_zero: sign 0 = 0 := rfl

-- -- °_° wtf
-- theorem sign_succ: sign ↑(succ a) = 1 := rfl

-- theorem zero_ne_one : (0 : myint) ≠ 1 :=
-- begin
--   rw [←one_nat, ←zero_nat],
--   assume h,
--   rw of_nat_cancel at h,
--   from zero_ne_one h,
-- end
