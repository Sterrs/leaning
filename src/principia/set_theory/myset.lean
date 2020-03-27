import principia.lt
import logic.basic

namespace hidden

universes u v w

-- A set of elements of type α is a function from elements of type α
-- to propositions
def myset (α : Type u) := α → Prop

namespace myset -- Not sure if we want this, but I don't think it hurts

-- Need u and v to be most general
variables {α : Type u} {β : Type v}

def mem (a : α) (s : myset α) : Prop := s a
instance: has_mem α (myset α) := ⟨myset.mem⟩

def subset (s : myset α) (t : myset α) : Prop :=
∀ a : α, s a → t a
-- Use \subseteq
instance: has_subset (myset α) := ⟨myset.subset⟩

def power_set (s : myset α) : myset (myset α) :=
λ t, t ⊆ s

def intersection (s : myset α) (t : myset α) : myset α :=
λ a, s a ∧ t a
instance: has_inter (myset α) := ⟨intersection⟩
def union (s : myset α) (t : myset α) : myset α :=
λ a, s a ∨ t a
instance: has_union (myset α) := ⟨union⟩

-- Construct an empty set with type α
def empty_of (α : Type u) : myset α := λ a, false
def empty {α : Type u} (s : myset α) : Prop := ∀ a : α, ¬(a ∈ s)
def all_of (α : Type u) : myset α := λ a, true

end myset

end hidden
