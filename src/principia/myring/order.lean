import .basic

namespace hidden

class ordered_myring (α : Type) [has_add α] [has_zero α] [has_neg α]
[has_mul α] [has_one α] [myring α] [has_le α] :=
(le_add_right (a b c : α) : a ≤ b → a + c ≤ b + c)
(zero_le_mul (a b : α) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

namespace ordered_myring

end ordered_myring

end hidden
