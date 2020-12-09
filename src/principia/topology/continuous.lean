import .topological_space

namespace hidden

namespace topological_space

variables {α β : Type}

def is_continuous (f : α → β) [X : topological_space α] [Y : topological_space β] : Prop :=
∀ V : myset β, is_open Y V → is_open X (myset.inverse_image f V)

-- e.g. Identity, constant, inclusion functions are cts

end topological_space

end hidden
