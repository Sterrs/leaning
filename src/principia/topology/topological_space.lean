-- vim: ts=2 sw=0 sts=-1 et ai tw=70

-- Note we're not currently transitioning over to hidden namespace - we probably should,
-- though it will break things

structure topological_space (α : Type) :=
(is_open : set (set α))
(univ_open : is_open set.univ)
(empty_open : is_open ∅)
(open_union_open (σ : set (set α)): σ ⊆ is_open → is_open ⋃₀ σ)
(open_intersection_open (U V : set α) : is_open U → is_open V → is_open (U ∩ V))

-- Don't know what this does
-- attribute [class] topological_space

namespace function -- This is an actual Lean namespace!!!

def image {α β : Type} (f : α → β) (U : set α) := {b | ∃ a, a ∈ U ∧ f a = b}

def inverse_image {α β : Type} (f : α → β) (V : set β) := {a | f a ∈ V}

end function


namespace set -- This is an actual Lean namespace!!!

variables {α β : Type}

def prod (U : set α) (V : set β) : set (α × β) :=
{t | t.1 ∈ U ∧ t.2 ∈ V}

notation U × V := prod U V

end set

namespace topological_space

variables {α β : Type}
-- include X Y

-- We don't assume a topology and define a base, we *build* a topology from a base
def is_base (B : set (set α)) :=
set.univ ∈ B ∧ ∀ b₁ b₂: set α, b₁ ∈ B → b₂ ∈ B → b₁ ∩ b₂ ∈ B

-- Given a suitable set, build a topological space with it as a base.
def space_from_base (B : set (set α)) (hB : is_base B) : topological_space α :=
{
  is_open := λ U, (∀ x : α, x ∈ U → (∃ b, b ∈ B ∧ x ∈ b ∧ b ⊆ U)),
  univ_open :=
  begin
    unfold is_base at hB,
    intro x,
    assume h,
    existsi set.univ,
    split,
      from hB.left,
    split,
      from h,
    intro y,
    assume hy,
    assumption,
  end,
  empty_open :=
  begin
    intro x,
    assume h,
    exfalso,
    from h,
  end,
  open_union_open :=
  begin
    intro σ,
    assume hσ,
    intro x,
    assume hx,
    cases hx with Uj hUj, -- Zsak called it U_j in his proof
    cases hUj with hUj hxUj, -- ???
    have h := hσ hUj,
    cases h x hxUj with b hb,
    existsi b,
    split,
      from hb.left,
    split,
      from hb.right.left,
    intro y,
    assume hy,
    existsi Uj,
    existsi hUj,
    from hb.right.right hy,
  end,
  open_intersection_open :=
  begin
    unfold is_base at hB,
    intros U V,
    assume hU hV,
    intro x,
    assume hUV,
    cases hU x (hUV.left) with b₁ hb₁,
    cases hV x (hUV.right) with b₂ hb₂,
    existsi b₁ ∩ b₂,
    split,
      apply hB.right,
        from hb₁.left,
      from hb₂.left,
    split,
      split,
        from hb₁.right.left,
      from hb₂.right.left,
    intro y,
    assume hy,
    split,
      from hb₁.right.right hy.left,
    from hb₂.right.right hy.right,
  end
}

def product_base (X : topological_space α) (Y : topological_space β) : set (set (α × β)) :=
{ b | ∃ (U : set α) (V : set β), b = (U × V) ∧ is_open X U ∧ is_open Y V }

theorem is_base_product_base (X : topological_space α) (Y : topological_space β) :
is_base (product_base X Y) :=
begin
  split,
    existsi set.univ,
    existsi set.univ,
    split,
      apply funext,
      intro x,
      apply propext,
      split; assume h,
      split; trivial,
      trivial,
    split,
      from X.univ_open,
    from Y.univ_open,
  intros b₁ b₂,
  assume hb₁ hb₂,
  cases hb₁ with U₁ this,
  cases this with V₁ this,
  cases this with hb₁ this,
  cases this with hU₁ hV₁,
  cases hb₂ with U₂ this,
  cases this with V₂ this,
  cases this with hb₂ this,
  cases this with hU₂ hV₂,
  existsi U₁ ∩ U₂,
  existsi V₁ ∩ V₂,
  split,
    -- This should be general theorem (U₁ × V₁) ∩ (U₂ × V₂) = (U₁ ∩ U₂ × V₁ ∩ V₂)
    subst b₁, subst b₂,
    apply funext,
    intro x,
    apply propext,
    split; assume h,
      cases h with h₁ h₂,
      cases h₁ with hxU₁ hxV₁,
      cases h₂ with hxU₂ hxV₂,
      split; split; assumption, -- :) semicolons are nice
    cases h with hU hV,
    cases hU with hxU₁ hxU₂,
    cases hV with hxV₁ hxV₂,
    split; split; assumption,
  split,
    apply X.open_intersection_open; assumption,
  apply Y.open_intersection_open; assumption,
end

def product_topology (X : topological_space α) (Y : topological_space β) :
topological_space (α × β) := space_from_base (product_base X Y) (is_base_product_base X Y)

-- TODO: Theorem which actually makes the product topology usable: what is an open set?

def is_continuous (f : α → β) [X : topological_space α] [Y : topological_space β] : Prop :=
∀ V : set β, is_open Y V → is_open X (function.inverse_image f V)

def discrete_topology (α : Type) : topological_space α :=
{
  is_open := λ U, true,
  univ_open := trivial,
  empty_open := trivial,
  open_union_open := λ σ h, trivial,
  open_intersection_open := λ U V hU hV, trivial,
}

def indiscrete_topology (α : Type) : topological_space α :=
{
  is_open := λ U, U = ∅ ∨ U = set.univ,
  univ_open := begin
    right,
    refl,
  end,
  empty_open := begin
    left,
    refl,
  end,
  open_union_open := λ σ h,
  begin
    sorry,
  end,
  open_intersection_open := λ U V hU hV,
  begin
    cases hU; cases hV, {
      left,
      rw [hU, hV],
      -- Now we are proving ∅ ∩ ∅ = ∅
      apply funext,     -- *
      intro x,          -- * These three lines are effectively `apply setext`
      apply propext,    -- *
      split; assume h,
      exact h.left,
      exact ⟨h,h⟩,
    }, {
      left,
      apply funext,
      intro x,
      apply propext,
      subst hU, subst hV,
      split; assume h,
        from h.left,
      split,
        from h,
      unfold set.univ,
    }, {
      left,
      apply funext,
      intro x,
      apply propext,
      subst hU, subst hV,
      split; assume h,
        from h.right,
      split,
        unfold set.univ,
      from h,
    }, {
      right,
      apply funext,
      intro x,
      apply propext,
      subst hU, subst hV,
      split; assume h,
        unfold set.univ,
      split; unfold set.univ,
    },
  end
}

def is_disconnected (X : topological_space α) : Prop :=
∃ U V : set α, U ≠ ∅ ∧ V ≠ ∅ ∧ is_open X U ∧ is_open X V ∧ U ∩ V = ∅ ∧ U ∪ V = set.univ

def is_connected (X : topological_space α) : Prop :=
¬is_disconnected X

end topological_space
