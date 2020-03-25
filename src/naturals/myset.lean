import naturals.lt
import logic.basic

namespace hidden

universes u v

-- A set of elements of type α is a function from elements of type α
-- to propositions
def myset (α : Type u) := α → Prop

namespace myset

section definitions
-- Need u and v to be most general
parameters {α : Type u} {β : Type v}

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

def empty (α : Type u) : myset α := λ a, false
def all_of (α : Type u) : myset α := λ a, true

-- Exclude the actual value so there are m elements
def zero_to (m : mynat) : myset mynat := λ n, n < m

section funcs
-- In this section we will consider types α and β with sets s and t
-- and a function f between them
parameters (s : myset α) (t : myset β) (f : α → β)

include s t f

-- A function between two sets is well-defined so long as each element
-- of the first gets sent to an element of the latter
def well_defined : Prop :=
∀ a : α, a ∈ s → f a ∈ t

-- Let's assume f is well-defined from s to t for now.
parameter (h : well_defined)

include h

def injective: Prop :=
∀ a₁ a₂ : α, a₁ ∈ s → a₂ ∈ s → a₁ ≠ a₂ → f a₁ ≠ f a₂
def surjective: Prop :=
∀ b : β, b ∈ t → ∃ a : α, a ∈ s ∧ f a = b

def bijective: Prop := injective ∧ surjective

end funcs

-- Is it possible to actually create the type of cardinal, then do
-- cardinal arithmetic

def card_le (s : myset α) (t : myset β) : Prop :=
∃ f : α → β, ∃ h: well_defined s t f, (injective s t f h)
def card_ge (s : myset α) (t : myset β) : Prop :=
∃ f : α → β, ∃ h: well_defined s t f, (surjective s t f h)
-- of same cardinality
def equinumerous (s : myset α) (t : myset β) : Prop :=
∃ f : α → β, ∃ h: well_defined s t f, (bijective s t f h)

end definitions

def finite {α : Type u} (s : myset α) : Prop :=
∃ m : mynat, equinumerous s (zero_to m)
def infinite {α : Type u} (s : myset α) : Prop := ¬finite s
def countable {α : Type u} (s : myset α) : Prop :=
finite s ∨ equinumerous (all_of mynat) s
def uncountable {α : Type u} (s : myset α) : Prop :=
¬countable s

section theorems

variables {α : Type u} {β : Type v}

-- The trivial function from a set to itself is well defined
theorem trivial_well_defined (s : myset α):
well_defined s s (λ a, a) :=
begin
  intro a,
  assume h,
  assumption,
end
theorem trivial_injective (s : myset α):
injective s s (λ a, a) (trivial_well_defined s) :=
begin
  intros a₁ a₂,
  assume h₁ h₂ hneq,
  assumption,
end
theorem trivial_surjective (s : myset α):
surjective s s (λ a, a) (trivial_well_defined s) :=
begin
  intro a,
  assume h,
  existsi a,
  split,
    from h,
  refl,
end

@[refl]
theorem card_le_refl (s : myset α) :
card_le s s :=
begin
  let f := (λ a : α, a),
  let h := trivial_well_defined s,
  existsi f,
  existsi h,
  from trivial_injective s,
end
@[refl]
theorem card_ge_refl (s : myset α) :
card_ge s s :=
begin
  let f := (λ a : α, a),
  let h := trivial_well_defined s,
  existsi f,
  existsi h,
  from trivial_surjective s,
end
@[refl]
theorem equinumerous_refl (s : myset α) :
equinumerous s s :=
begin
  let f := (λ a : α, a),
  have h := trivial_well_defined s,
  existsi f,
  existsi h,
  split,
    from trivial_injective s,
  from trivial_surjective s,
end

open classical
local attribute [instance] prop_decidable

theorem card_ne_power_set (s : myset α) :
¬equinumerous s (power_set s) :=
begin
  assume heq,
  cases heq with f hf,
  cases hf with hwell hbi,
  cases hbi with hinj hsurj,
  suffices hcontra : ∃ t : myset α, t ∈ (power_set s) ∧
                     ∀ a : α, a ∈ s → f a ≠ t, {
    cases hcontra with t ht,
    cases hsurj t ht.left with preim hpreim,
    from ht.right preim hpreim.left hpreim.right,
  },
  let t := λ a : α, a ∈ s ∧ ¬(a ∈ f a),
  existsi t,
  split, {
    intro a,
    assume hta,
    from hta.left,
  }, {
    intro a,
    assume h heq,
    have hnta : ¬(t a), {
      assume hta,
      have haninfa := hta.right,
      rw heq at haninfa,
      contradiction,
    },
    have hta : t a, {
      rw not_and at hnta,
      have hnin := hnta h,
      rw [not_not, heq] at hnin,
      from hnin,
    },
    contradiction,
  },
end

theorem uncountability_of_power_set_of_naturals :
uncountable (power_set (all_of mynat)) :=
begin
  assume h,
  cases h with hfinite hcountinf, {
    -- Still need to prove the power set of the naturals is not
    -- finite, which seems hard, could use transitivity theorem?
    sorry,
  }, {
    have := card_ne_power_set (all_of mynat),
    contradiction,
  },
end

theorem schroeder_bernstein_theorem
{s : myset α} {t : myset β}:
card_le s t → card_ge s t → equinumerous s t := sorry

end theorems

end myset

end hidden
