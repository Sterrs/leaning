-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..logic

namespace hidden

universes u v w

-- A set of elements of type α is a function from elements of type α
-- to propositions
def myset (α : Type u) := α → Prop

 -- Not sure if we want this, but I don't think it hurts
namespace myset

-- Need u and v to be most general
variables {α : Type u} {β : Type v}

def mem (a : α) (s : myset α) : Prop := s a
instance: has_mem α (myset α) := ⟨myset.mem⟩

theorem mem_def {a : α} {s : myset α} : a ∈ s = s a := rfl

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

theorem exists_iff_nempty {s : myset α} :
(∃ x, x ∈ s) ↔ ¬empty s :=
begin
  split; assume h, {
    assume hemp,
    cases h with x hx,
    have := hemp x,
    contradiction,
  }, {
    unfold myset.empty at h,
    rw not_forall at h,
    cases h with k hk,
    existsi k,
    rw not_not at hk,
    assumption,
  },
end

-- Set product, gives myset (α × β)
def set_prod (U : myset α) (V : myset β) : myset (α × β) :=
{t | t.1 ∈ U ∧ t.2 ∈ V}

notation U × V := set_prod U V

instance : has_emptyc (myset α) :=
⟨λ a, false⟩

@[reducible]
def sUnion (s : myset (myset α)) : myset α := {t | ∃ a ∈ s, t ∈ a}
prefix `⋃₀`:120 := sUnion

def univ : myset α :=
λ a, true

def image {α β : Type} (f : α → β) (U : myset α) := {b | ∃ a, a ∈ U ∧ f a = b}

def inverse_image {α β : Type} (f : α → β) (V : myset β) := {a | f a ∈ V}

end myset

end hidden
