import .topological_space

namespace hidden

namespace topological_space

variables {α β : Type}

def is_disconnected (X : topological_space α) : Prop :=
∃ U V : myset α, U ≠ ∅ ∧ V ≠ ∅ ∧ is_open X U ∧ is_open X V ∧ U ∩ V = ∅ ∧ U ∪ V = myset.univ

def is_connected (X : topological_space α) : Prop :=
¬is_disconnected X

end topological_space

end hidden
