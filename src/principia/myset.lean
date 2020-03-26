import principia.lt
import logic.basic

namespace hidden

universes u v w

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

def empty_of (α : Type u) : myset α := λ a, false
def empty {α : Type u} (s : myset α) : Prop := ∀ a : α, ¬(a ∈ s)
def all_of (α : Type u) : myset α := λ a, true

-- Exclude the actual value so there are m elements
def zero_to (m : mynat) : myset mynat := λ n, n < m

theorem emp_zero_to_zero : empty (zero_to 0) :=
begin
  intro m,
  assume hm,
  from (lt_nzero m) hm,
end

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
∀ a₁ a₂ : α, a₁ ∈ s → a₂ ∈ s → f a₁ = f a₂ → a₁ = a₂
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

def of_size {α : Type u} (s : myset α) (m : mynat) : Prop :=
equinumerous s (zero_to m)
def finite {α : Type u} (s : myset α) : Prop :=
∃ m : mynat, of_size s m
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

theorem schroeder_bernstein_theorem
{s : myset α} {t : myset β}:
card_le s t → card_ge s t → equinumerous s t := sorry

end theorems

-- Theorems about two functions between sets
section function_composition

parameters {α : Type u} {β : Type v} {γ : Type w}
parameters (r : myset α) (s : myset β) (t : myset γ)
parameters (f : α → β) (g : β → γ)

open classical
local attribute [instance] prop_decidable

theorem no_wdefined_func_nemp_to_emp
(s : myset α) (t : myset β) (f : α → β)
{hemp : empty t} {hnemp : ¬empty s}:
¬well_defined s t f
:=
begin
  assume h,
  unfold empty at hnemp,
  rw not_forall at hnemp,
  cases hnemp with x hx,
  simp at hx,
  have hfxin := h x hx,
  have hfxnin := hemp (f x),
  contradiction,
end

theorem composition_well_defined:
well_defined r s f → well_defined s t g → well_defined r t (g ∘ f) :=
begin
  assume hwf hwg,
  intro a,
  assume har,
  apply hwg,
  apply hwf,
  assumption,
end

theorem inj_inj (hwf: well_defined r s f) (hwg: well_defined s t g):
injective r s f hwf → injective s t g hwg
  → injective r t (g ∘ f) (composition_well_defined hwf hwg) :=
begin
  assume hif hig,
  intros a b,
  assume har hbr hgfagfb,
  apply hif _ _ har hbr,
  apply hig _ _ (hwf a har) (hwf b hbr),
  assumption,
end

-- not the prettiest
theorem surj_surj (hwf: well_defined r s f) (hwg: well_defined s t g):
surjective r s f hwf → surjective s t g hwg
  → surjective r t (g ∘ f) (composition_well_defined hwf hwg) :=
begin
  assume hsf hsg,
  intro a,
  assume hat,
  cases hsg a hat with a_g ha_g,
  cases hsf a_g ha_g.left with a_f ha_f,
  existsi a_f,
  split, {
    from ha_f.left,
  }, {
    rw [←ha_g.right, ←ha_f.right],
  },
end

theorem bij_bij (hwf: well_defined r s f) (hwg: well_defined s t g):
bijective r s f hwf → bijective s t g hwg
  → bijective r t (g ∘ f) (composition_well_defined hwf hwg) :=
begin
  assume hbf hbg,
  cases hbf with hif hsf,
  cases hbg with hig hsg,
  split, {
    -- nice. wish I understood how all the fancy stuff works
    from inj_inj _ _ _ _ _ _ _ hif hig,
  }, {
    from surj_surj _ _ _ _ _ _ _ hsf hsg,
  }
end

end function_composition

section cardinality

parameters {α : Type u} {β : Type v} {γ : Type w}
parameters (r : myset α) (s : myset β) (t : myset γ)
parameters (f : α → β) (g : β → γ)
parameter (hwf : well_defined r s f)

include hwf

def restriction (r': myset α):
r' ⊆ r → (α → β) := (λ _ a, f a)

theorem restriction_well_defined
(r': myset α) (hrss: r' ⊆ r):
well_defined r' s (restriction r' hrss) :=
begin
  intro a,
  assume har',
  apply hwf,
  apply hrss,
  from har',
end

-- this can probably be shorter but I keep getting confused
-- by all the definitions
theorem restriction_injective
(r': myset α) (hrss: r' ⊆ r)
(hif: injective r s f hwf):
injective r' s (restriction r' hrss)
  (restriction_well_defined _ _) :=
begin
  intros a b,
  assume har' hbr' hrarb,
  apply hif _ _ _ _ _, {
    from hrss _ har',
  }, {
    from hrss _ hbr',
  }, {
    from hrarb,
  },
end

omit hwf

-- function swapping two naturals. Turns out this is harder
-- to define than I thought
def swap_naturals (a b x: mynat): mynat :=
sorry

-- pigeonhole principle, basically
-- have I overthought this?
-- and can this be done without classical? probably..
theorem no_injection_from_zero_to_succ
(n: mynat) (f: mynat → mynat)
(hwf: well_defined (zero_to (n + 1)) (zero_to n) f):
¬injective _ _ f hwf :=
begin
  assume h,
  induction n with n hn, {
    apply no_wdefined_func_nemp_to_emp (zero_to 1) (zero_to 0) f, {
      from hwf,
    }, {
      from emp_zero_to_zero,
    }, {
      assume h,
      have : (0 : mynat) ∈ zero_to 1, {
        from zero_lt_one,
      },
      from h 0 this,
    },
  }, {
    -- we are trying to show that if
    -- f: {0, ..., n + 1} → {0, ...,  n}
    -- is well-defined then it is not injective.
    -- Consider the pre-image of n. By injectivity,
    -- this at most one number. If it's empty, skip to
    -- the restriction. If not, call it x.
    -- Define f': {0, ..., n + 1} → {0, ..., n}
    -- by composing f with the function swapping n + 1 and x.
    -- This function is still injective and has n + 1 ↦ n,
    -- so we can restrict it to {0, ..., n} and its range will
    -- restrict to {0, ..., n - 1}. Then we are done by induction.
    let s: myset mynat := (λ k, f k = n),
    sorry,
  },
end

theorem naturals_infinite: infinite (all_of mynat) :=
begin
  assume hfinite,
  cases hfinite with n hn,
  cases hn with f hf,
  cases hf with hwf h,
  sorry,
end

theorem inf_iff_powerset_inf (s : myset α):
infinite s ↔ infinite (power_set s) :=
begin
  split; assume hinf, {
    sorry,
  }, {
    sorry,
  }
end

theorem uncountability_of_power_set_of_naturals:
uncountable (power_set (all_of mynat)) :=
begin
  assume h,
  cases h with hfinite hcountinf, {
    -- Using revert here is quite nice
    revert hfinite,
    -- Although this line is stupid
    suffices : infinite (power_set (all_of mynat)), from this,
    rw ←inf_iff_powerset_inf (all_of mynat),
    from naturals_infinite,
  }, {
    have := card_ne_power_set (all_of mynat),
    contradiction,
  },
end

end cardinality

end myset

end hidden
