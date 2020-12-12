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
