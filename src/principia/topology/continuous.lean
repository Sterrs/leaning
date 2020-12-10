import .topological_space

namespace hidden

namespace topological_space

variables {α β : Type}

open classical

local attribute [instance] classical.prop_decidable

def is_continuous (f : α → β) [X : topological_space α] [Y : topological_space β] : Prop :=
∀ V : myset β, is_open Y V → is_open X (myset.inverse_image f V)

-- e.g. Identity, constant, inclusion functions are cts

theorem identity_continuous [X : topological_space α]:
@is_continuous _ _ (id: α → α) X X :=
begin
  intro V,
  assume hoV,
  have: V = myset.inverse_image id V := rfl,
  rw ←this,
  assumption,
end

theorem constant_continuous
[X : topological_space α] [Y : topological_space β]
(y: β):
@is_continuous α β (λ x, y) X Y :=
begin
  intro V,
  assume hoV,
  by_cases hy: y ∈ V, {
    have: (myset.inverse_image (λ (x : α), y) V) = myset.univ,  {
      apply funext,
      intro x,
      apply propext,
      split; assume h, {
        trivial,
      }, {
        from hy,
      },
    },
    rw this,
    from X.univ_open,
  }, {
    have: (myset.inverse_image (λ (x : α), y) V) = ∅, {
      apply funext,
      intro x,
      apply propext,
      split; assume h, {
        trivial,
      }, {
        exfalso, from h,
      },
    },
    rw this,
    from X.empty_open,
  },
end

theorem inclusion_continuous
[X : topological_space α] (Y: myset α):
@is_continuous (subtype Y) α (λ x, x) (subspace_topology X Y) X :=
begin
  intro V,
  assume hoV,
  existsi V,
  split, {
    assumption,
  }, {
    refl,
  },
end

end topological_space

end hidden
