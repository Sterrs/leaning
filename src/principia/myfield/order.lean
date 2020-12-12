import .basic

namespace hidden

-- Can't extend field and ordered_myring as they both extend myring >:(
class ordered_myfield (α : Type) [has_le α] [ordered_myring α] extends myfield α

namespace ordered_myfield

variables {α : Type} [has_le α] [ordered_myring α] [ordered_myfield α] (x y z : α)
variables (s t : α) -- Try to use s, t when non-zero



end ordered_myfield

end hidden