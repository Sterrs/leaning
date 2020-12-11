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

@[refl]
theorem subset_refl (s: myset α):
s ⊆ s :=
begin
  intro x,
  assume h,
  assumption,
end

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

theorem empty_iff_eq_empty {s: myset α}: empty s ↔ s = ∅ :=
begin
  split; assume h, {
    apply funext,
    intro a,
    have := h a,
    apply propext,
    split, {
      assume hs, contradiction,
    }, {
      assume he,
      exfalso,
      from he,
    },
  }, {
    intro a,
    assume hs,
    rw h at hs,
    from hs,
  },
end

@[reducible]
def sUnion (s : myset (myset α)) : myset α := {t | ∃ a ∈ s, t ∈ a}
prefix `⋃₀`:120 := sUnion

@[reducible]
def sIntersection (s : myset (myset α)) : myset α :=
{t | ∀ a ∈ s, t ∈ a}
prefix `⋂₀`:120 := sIntersection

def univ : myset α :=
λ a, true

def image {α β : Type} (f : α → β) (U : myset α) := {b | ∃ a, a ∈ U ∧ f a = b}

def inverse_image {α β : Type} (f : α → β) (V : myset β) := {a | f a ∈ V}

theorem inverse_image_of_image
{α β : Type} (f: α → β) (U : myset α):
U ⊆ inverse_image f (image f U) :=
begin
  intro x,
  assume hx,
  existsi x,
  split, assumption, trivial,
end

theorem image_of_inverse_image
{α β : Type} (f: α → β) (U : myset β):
image f (inverse_image f U) ⊆ U :=
begin
  intro x,
  assume hx,
  cases hx with y hy,
  rw ←hy.right,
  from hy.left,
end

theorem subset_empty_impl_empty
{α: Type} (U: myset α):
U ⊆ ∅ → U = ∅ :=
begin
  assume hUe,
  apply funext,
  intro x,
  apply propext,
  split; assume h, {
    from hUe _ h,
  }, {
    exfalso, from h,
  },
end

theorem univ_subset_impl_univ
{α: Type} (U: myset α):
myset.univ ⊆ U → U = myset.univ :=
begin
  assume h,
  apply funext,
  intro x,
  apply propext,
  split; assume hux, {
    trivial,
  }, {
    from h x trivial,
  },
end

theorem image_nonempty
{α β : Type} (f: α → β) (U: myset α):
U ≠ ∅ → image f U ≠ ∅ :=
begin
  assume hUne,
  assume hpreUe,
  rw ←empty_iff_eq_empty at hpreUe,
  change ¬(U = ∅) at hUne,
  rw ←empty_iff_eq_empty at hUne,
  rw ←exists_iff_nempty at hUne,
  cases hUne with x hx,
  apply hpreUe (f x),
  existsi x,
  split, assumption, refl,
end

theorem image_empty
{α β : Type} (f: α → β) (U: myset α):
U = ∅ → image f U = ∅ :=
begin
  assume hUe,
  apply funext,
  intro x,
  apply propext,
  split; assume h, {
    cases h with y hy,
    rw hUe at hy,
    from hy.left,
  }, {
    exfalso, from h,
  },
end

theorem inverse_image_empty
{α β : Type} (f: α → β) (U: myset β):
U = ∅ → inverse_image f U = ∅ :=
begin
  assume hUe,
  apply funext,
  intro x,
  apply propext,
  split; assume h, {
    rw hUe at h,
    from h,
  }, {
    exfalso, from h,
  },
end

theorem inverse_image_intersection
{α β : Type} (f: α → β) (U V: myset β):
inverse_image f (U ∩ V) = inverse_image f U ∩ inverse_image f V :=
begin
  refl,
end

theorem inverse_image_union
{α β : Type} (f: α → β) (U V: myset β):
inverse_image f (U ∪ V) = inverse_image f U ∪ inverse_image f V :=
begin
  refl,
end

theorem inverse_image_composition
{α β γ: Type} (f: α → β) (g: β → γ) (U: myset γ):
inverse_image (g ∘ f) U =
inverse_image f (inverse_image g U) :=
begin
  apply funext,
  intro x,
  apply propext,
  refl,
end

theorem inverse_image_of_image_of_univ
{α β : Type} (f: α → β):
myset.univ = inverse_image f (image f myset.univ) :=
begin
  symmetry,
  apply univ_subset_impl_univ,
  apply inverse_image_of_image,
end

def compl (s : myset α) : myset α :=
{a | a ∉ s}

-- Used to restrict some set to a subtype ("intersect" a set with a subtype)
def subtype_restriction (Y : myset α) (U : myset α) : myset (subtype Y) :=
{ w | ↑w ∈ U }

def function_restrict_to_image
{α β: Type} (f: α → β): α → subtype (myset.image f myset.univ)
:= λ x, ⟨f x, ⟨x, ⟨true.intro, rfl⟩⟩⟩

theorem to_image_surjective
{α β: Type} (f: α → β):
(image (function_restrict_to_image f) univ) = univ :=
begin
  apply funext,
  intro x,
  apply propext,
  split; assume h, {
    trivial,
  }, {
    cases x.property with y hy,
    unfold image,
    existsi y,
    split, {
      trivial,
    }, {
      apply subtype.eq,
      rw ←hy.right,
      refl,
    },
  },
end

theorem nonempty_inverse_image_surjective
{α β: Type} (f: α → β) (U: myset (subtype (image f univ))):
U ≠ ∅ →
inverse_image (function_restrict_to_image f) U ≠ ∅ :=
begin
  assume hUne,
  assume hpreUe,
  rw ←empty_iff_eq_empty at hpreUe,
  change ¬(U = ∅) at hUne,
  rw ←empty_iff_eq_empty at hUne,
  rw ←exists_iff_nempty at hUne,
  cases hUne with x hx,
  cases x.property with y hy,
  apply hpreUe y,
  unfold inverse_image,
  have: x = ⟨f y, begin rw hy.right, from x.property end⟩, {
    apply subtype.eq,
    from hy.right.symm,
  },
  rw this at hx, clear this,
  from hx,
end

end myset

end hidden
