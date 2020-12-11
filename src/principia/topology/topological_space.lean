-- vim: ts=2 sw=0 sts=-1 et ai tw=70

-- Note we're not currently transitioning over to hidden namespace - we probably should,
-- though it will break things

import ..myset.basic
import ..myset.finite
import ..mylist.map

namespace hidden

structure topological_space (α : Type) :=
(is_open : myset (myset α))
(univ_open : is_open myset.univ)
(empty_open : is_open ∅)
(open_union_open (σ : myset (myset α)): σ ⊆ is_open → is_open ⋃₀ σ)
(open_intersection_open (U V : myset α) : is_open U → is_open V → is_open (U ∩ V))

-- Don't know what this does
-- attribute [class] topological_space

namespace topological_space

open classical

local attribute [instance] classical.prop_decidable

variables {α β : Type}
-- include X Y

def is_hausdorff (X : topological_space α) : Prop :=
∀ x y : α, x ≠ y →
  ∃ (U V : myset α),
    is_open X U ∧ is_open X V ∧ x ∈ U ∧ y ∈ V ∧ U ∩ V = ∅

def is_closed (X : topological_space α) (A : myset α) : Prop :=
is_open X (myset.compl A)

-- An attempt to create subspaces
def subspace_topology (X : topological_space α) (Y : myset α) : topological_space (subtype Y) :=
{
  is_open := { V | ∃ U : myset α, is_open X U ∧ V = myset.subtype_restriction Y U },
  univ_open :=
  begin
    existsi myset.univ,
    split, {
      from X.univ_open,
    }, {
      apply funext,
      intro x,
      refl,
    },
  end,
  empty_open :=
  begin
    -- it does weird things if i try ∅
    existsi (λ x, false),
    split, {
      from X.empty_open,
    }, {
      apply funext,
      intro x,
      refl,
    },
  end,
  open_union_open :=
  begin
    intros σ hσ,
    let τ : myset (myset α) :=
    {W | X.is_open W ∧ ∃ V : myset (subtype Y), V ∈ σ ∧ V = Y.subtype_restriction W},
    existsi ⋃₀τ,
    split, {
      apply X.open_union_open,
      intros U hU,
      from hU.left,
    }, {
      unfold myset.subtype_restriction,
      apply funext,
      intro x,
      apply propext,
      split; assume h, {
        cases h with W hW,
        cases hW with hWσ hxW,
        cases hσ _ hWσ with U hU,
        existsi U,
        cases hU with hUopen hWU,
        suffices : U ∈ τ,
          existsi this,
          rwa hWU at hxW,
        split,
          assumption,
        existsi W,
        split; assumption,
      }, {
        cases h with V hV,
        cases hV with hVτ hxV,
        existsi Y.subtype_restriction V,
        cases hVτ with hVopen this,
        cases this with U this,
        cases this with hUσ hUV,
        rw hUV at hUσ,
        existsi hUσ,
        assumption,
      },
    },
  end,
  open_intersection_open :=
  begin
    intros U V,
    assume hU hV,
    cases hU with U' hU',
    cases hV with V' hV',
    existsi U' ∩ V',
    split, {
      apply X.open_intersection_open, {
        from hU'.left,
      }, {
        from hV'.left,
      },
    }, {
      apply funext,
      intro x,
      apply propext,
      split, {
        assume hUVx,
        split, {
          have := hUVx.left,
          rw hU'.right at this,
          from this,
        }, {
          have := hUVx.right,
          rw hV'.right at this,
          from this,
        },
      }, {
        assume hUVx,
        split, {
          rw hU'.right,
          from hUVx.left,
        }, {
          rw hV'.right,
          from hUVx.right,
        },
      },
    },
  end
}

-- We don't assume a topology and define a base, we *build* a topology from a base
def is_base (B : myset (myset α)) :=
myset.univ ∈ B ∧ ∀ b₁ b₂: myset α, b₁ ∈ B → b₂ ∈ B → b₁ ∩ b₂ ∈ B

-- Given a suitable myset, build a topological space with it as a base.
def space_from_base (B : myset (myset α)) (hB : is_base B) : topological_space α :=
{
  is_open := λ U, (∀ x : α, x ∈ U → (∃ b, b ∈ B ∧ x ∈ b ∧ b ⊆ U)),
  univ_open :=
  begin
    unfold is_base at hB,
    intro x,
    assume h,
    existsi myset.univ,
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
    have h := hσ Uj hUj,
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
    apply hb.right.right,
    from hy,
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
      apply hb₁.right.right,
      from hy.left,
    apply hb₂.right.right,
    from hy.right,
  end
}

def product_base (X : topological_space α) (Y : topological_space β) : myset (myset (α × β)) :=
{ b | ∃ (U : myset α) (V : myset β), b = (U × V) ∧ is_open X U ∧ is_open Y V }

theorem is_base_product_base (X : topological_space α) (Y : topological_space β) :
is_base (product_base X Y) :=
begin
  split,
    existsi myset.univ,
    existsi myset.univ,
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
  is_open := λ U, U = ∅ ∨ U = myset.univ,
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
    by_cases hempty: ⋃₀ σ = ∅, {
      left, assumption,
    }, {
      right,
      rw ←myset.empty_iff_eq_empty at hempty,
      rw ←myset.exists_iff_nempty at hempty,
      cases hempty with x hx,
      apply funext,
      intro y,
      apply propext,
      dsimp only [myset.univ],
      split; assume hy, {
        trivial,
      }, {
        dsimp only [myset.sUnion],
        dsimp only [myset.sUnion] at hx,
        cases hx with S hS,
        cases hS with H hH,
        cases h S H with he hu, {
          rw he at hH,
          exfalso, from hH,
        }, {
          existsi S,
          existsi H,
          rw hu,
          trivial,
        },
      },
    },
  end,
  open_intersection_open := λ U V hU hV,
  begin
    cases hU; cases hV, {
      left,
      rw [hU, hV],
      -- Now we are proving ∅ ∩ ∅ = ∅
      apply funext,     -- *
      intro x,          -- * These three lines are effectively `apply mysetext`
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
      unfold myset.univ,
    }, {
      left,
      apply funext,
      intro x,
      apply propext,
      subst hU, subst hV,
      split; assume h,
        from h.right,
      split,
        unfold myset.univ,
      from h,
    }, {
      right,
      apply funext,
      intro x,
      apply propext,
      subst hU, subst hV,
      split; assume h,
        unfold myset.univ,
      split; unfold myset.univ,
    },
  end
}

def interior (X : topological_space α) (A : myset α) : myset α :=
⋃₀ { U | is_open X U ∧ U ⊆ A }

def closure (X : topological_space α) (A : myset α) : myset α :=
⋂₀ { F | is_closed X F ∧ A ⊆ F }

def is_dense (X : topological_space α) (A : myset α) : Prop :=
closure X A = myset.univ

def is_neighbourhood (X: topological_space α) (U: myset α) (x: α): Prop :=
∃ V: myset α, X.is_open V ∧ x ∈ V ∧ V ⊆ U

-- turns out neighbourhoods are useful!!!
-- I like this theorem because it means I don't have to unironically write
-- down unions all the time
theorem open_iff_neighbourhood_forall
(X: topological_space α) (U: myset α):
X.is_open U ↔ ∀ x: α, x ∈ U → is_neighbourhood X U x :=
begin
  split, {
    assume hUo,
    intro x,
    assume hxU,
    existsi U,
    split, {
      assumption,
    }, split, {
      assumption,
    }, {
      refl,
    },
  }, {
    assume hUnbhd,
    have hunion := X.open_union_open
      {V | X.is_open V ∧ V ⊆ U}
      begin
        intro V,
        assume hV,
        from hV.left,
      end,
    suffices heq: (⋃₀{V : myset α | X.is_open V ∧ V ⊆ U}) = U, {
      rw ←heq,
      assumption,
    }, {
      apply funext,
      intro x,
      apply propext,
      split; assume h, {
        cases h with V hV,
        cases hV with hV hxV,
        apply hV.right,
        assumption,
      }, {
        cases hUnbhd x h with V hV,
        existsi V,
        split, split, {
          from hV.left,
        }, {
          from hV.right.right,
        }, {
          from hV.right.left,
        },
      },
    },
  },
end

theorem hausdorff_point_closed
(X: topological_space α) (h_ausdorff: is_hausdorff X)
(x: α):
is_closed X ({y: α | y = x}) :=
begin
  apply (open_iff_neighbourhood_forall _ _).mpr,
  intro y,
  assume hynex,
  cases h_ausdorff y x hynex with U hUV,
  cases hUV with V hUV,
  existsi U,
  split, {
    from hUV.left,
  }, split, {
    from hUV.right.right.left,
  }, {
    intro z,
    assume hUz,
    assume hzx,
    rw ←myset.empty_iff_eq_empty at hUV,
    apply hUV.right.right.right.right x,
    split, {
      have: z = x := hzx,
      rw ←this,
      assumption,
    }, {
      from hUV.right.right.right.left,
    },
  },
end

private lemma append_not_empty
(lst: mylist α) (x: α): lst ++ [x] ≠ [] :=
begin
  assume h,
  rw mylist.empty_iff_len_zero at h,
  rw mylist.len_concat_add at h,
  from mynat.succ_ne_zero h,
end

def list_open
(X: topological_space α) (σ: mylist (myset α)): Prop :=
mylist.reduce and (mylist.map X.is_open (σ ++ [myset.univ]))
begin
  rw mylist.map_concat,
  apply append_not_empty,
end

def list_intersection
(X: topological_space α) (σ: mylist (myset α)): myset α :=
mylist.reduce myset.intersection (σ ++ [myset.univ])
(append_not_empty _ _)

-- finite intersections of open set are open,
-- stated with lists
theorem finite_open_intersection_open
(X: topological_space α) (σ : mylist (myset α))
(hso: list_open X σ):
X.is_open (list_intersection X σ) :=
begin
  induction σ, {
    from X.univ_open,
  }, {
    cases σ_tail, {
      apply X.open_intersection_open, {
        from hso.left,
      }, {
        from X.univ_open,
      },
    }, {
      apply X.open_intersection_open, {
        from hso.left,
      }, {
        apply σ_ih,
        from hso.right,
      },
    },
  },
end

theorem topological_space_eq
(X: topological_space α) (Y: topological_space α):
X.is_open = Y.is_open → X = Y :=
begin
  -- idk how to prove this
  sorry,
end

theorem discrete_subspace
(S: myset α):
discrete_topology (subtype S) =
subspace_topology (discrete_topology α) S :=
begin
  apply topological_space_eq,
  apply funext,
  intro X,
  apply propext,
  split; assume h, {
    -- is this sensible ? ?
    existsi λ x, ∃ hxS: x ∈ S, (⟨x, hxS⟩: subtype S) ∈ X,
    split, {
      trivial,
    }, {
      apply funext,
      intro x,
      apply propext,
      split, {
        assume hx,
        existsi x.property,
        have: (⟨↑x, x.property⟩: subtype S) = x, {
          apply subtype.eq,
          refl,
        },
        rw this,
        from hx,
      }, {
        assume hx,
        cases hx with hX hx,
        have: (⟨↑x, hX⟩: subtype S) = x, {
          apply subtype.eq,
          refl,
        },
        rw ←this,
        from hx,
      },
    },
  }, {
    trivial,
  },
end

theorem indiscrete_subspace
(S: myset α):
indiscrete_topology (subtype S) =
subspace_topology (indiscrete_topology α) S :=
begin
  apply topological_space_eq,
  apply funext,
  intro X,
  apply propext,
  split; assume hXo, {
    cases hXo with hXe hXu, {
      rw hXe,
      apply topological_space.empty_open,
    }, {
      rw hXu,
      apply topological_space.univ_open,
    },
  }, {
    cases hXo with U hXo,
    cases hXo with hUo hXU,
    cases hUo with hUe hUu, {
      rw hUe at hXU,
      left,
      rw hXU,
      refl,
    }, {
      rw hUu at hXU,
      right,
      rw hXU,
      refl,
    },
  },
end

theorem empty_discrete: sorry := sorry

theorem empty_indiscrete: sorry := sorry

theorem singleton_discrete: sorry := sorry

theorem singleton_indiscrete (X: topological_space α) (x: α):
discrete_topology (subtype ({y | y = x})) =
subspace_topology X ({y | y = x}) :=
begin
  apply topological_space.rec,
  intros,
  symmetry,
  apply topological_space.rec,
  intros,
  simp, -- forgive me
  apply funext,
  intro S,
  apply propext,
  by_cases hSe: S = ∅, {
    rw hSe,
    split; assume h,
    assumption,
    assumption,
  }, {
    change S ≠ ∅ at hSe,
    rw ←myset.exists_iff_neq_empty at hSe,
    cases hSe with y hy,
    have: S = myset.univ, {
      apply funext,
      intro z,
      apply propext,
      split; assume h, {
        trivial,
      }, {
        have: y = z, {
          let x': subtype {y : α | y = x} := ⟨x, rfl⟩,
          transitivity x', {
            have := y.property,
            apply subtype.eq,
            from this,
          }, {
            symmetry,
            have := z.property,
            apply subtype.eq,
            from this,            
          },
        },
        rw this at hy,
        assumption,
      },
    },
    rw this,
    split; assume h,
    assumption,
    assumption,
  },
end

end topological_space
end hidden
