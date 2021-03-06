-- vim: ts=2 sw=0 sts=-1 et ai tw=70

-- Note we're not currently transitioning over to hidden namespace - we probably should,
-- though it will break things

import ..myset.basic
import ..myset.finite
import ..mylist.map
import ..logic

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

structure sets_separate_points
(X: topological_space α) (x y: α) (U V: myset α): Prop :=
(open_left: X.is_open U)
(open_right: X.is_open V)
(contains_left: x ∈ U)
(contains_right: y ∈ V)
(disjoint: U ∩ V = ∅)

def is_hausdorff (X : topological_space α) : Prop :=
∀ x y : α, x ≠ y →
  ∃ (U V : myset α),
    sets_separate_points X x y U V

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
      apply myset.setext,
      intro x,
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
      apply myset.setext,
      intro x,
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

structure is_box_of
(X: topological_space α) (Y: topological_space β)
(U: myset α) (V: myset β) (B: myset (α × β)): Prop :=
(eq: B = (U × V))
(open_left: X.is_open U)
(open_right: Y.is_open V)

def product_base (X : topological_space α) (Y : topological_space β) : myset (myset (α × β)) :=
{ B | ∃ (U : myset α) (V : myset β), is_box_of X Y U V B}

theorem is_base_product_base (X : topological_space α) (Y : topological_space β) :
is_base (product_base X Y) :=
begin
  split,
    existsi myset.univ,
    existsi myset.univ,
    split,
      apply myset.setext,
      intro x,
      split; assume h,
      split; trivial,
      trivial,
      from X.univ_open,
    from Y.univ_open,
  intros b₁ b₂,
  assume hb₁ hb₂,
  cases hb₁ with U₁ this,
  cases this with V₁ this,
  cases this with hb₁ this,
  cases hb₂ with U₂ this,
  cases this with V₂ this,
  cases this with hb₂ this,
  existsi U₁ ∩ U₂,
  existsi V₁ ∩ V₂,
  split,
    -- This should be general theorem (U₁ × V₁) ∩ (U₂ × V₂) = (U₁ ∩ U₂ × V₁ ∩ V₂)
    subst b₁, subst b₂,
    apply myset.setext,
    intro x,
    split; assume h,
      cases h with h₁ h₂,
      cases h₁ with hxU₁ hxV₁,
      cases h₂ with hxU₂ hxV₂,
      split; split; assumption, -- :) semicolons are nice
    cases h with hU hV,
    cases hU with hxU₁ hxU₂,
    cases hV with hxV₁ hxV₂,
    split; split; assumption,
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
      apply myset.setext,
      intro y,
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
      apply myset.setext,
      intro x,
      split; assume h,
      exact h.left,
      exact ⟨h,h⟩,
    }, {
      left,
      apply myset.setext,
      intro x,
      subst hU, subst hV,
      split; assume h,
        from h.left,
      split,
        from h,
      unfold myset.univ,
    }, {
      left,
      apply myset.setext,
      intro x,
      subst hU, subst hV,
      split; assume h,
        from h.right,
      split,
        unfold myset.univ,
      from h,
    }, {
      right,
      apply myset.setext,
      intro x,
      subst hU, subst hV,
      split; assume h,
        unfold myset.univ,
      split; unfold myset.univ,
    },
  end
}

def interior (X : topological_space α) (A : myset α) : myset α :=
⋃₀ { U | is_open X U ∧ U ⊆ A }

theorem interior_open (X : topological_space α) (A : myset α) : is_open X (interior X A) :=
begin
  apply X.open_union_open,
  intros U hU,
  from hU.left,
end

def closure (X : topological_space α) (A : myset α) : myset α :=
⋂₀ { F | is_closed X F ∧ A ⊆ F }

theorem closure_closed (X : topological_space α) (A : myset α) : is_closed X (closure X A) :=
begin
  unfold closure,
  unfold is_closed,
  rw myset.compl_sIntersection,
  apply open_union_open,
  intros S hS,
  cases hS with T hT,
  rw ←hT.right,
  from hT.left.left,
end

theorem compl_interior_compl_eq_closure (X : topological_space α) (A : myset α) :
(X.interior A.compl).compl = X.closure A :=
begin
  unfold interior,
  rw myset.compl_sUnion,
  congr,
  apply myset.setext,
  intro S,
  split; assume hS,
    cases hS with T hT,
    rw hT.right.symm,
    split,
      unfold is_closed,
      rw myset.compl_compl,
      from hT.left.left,
    apply myset.subset_compl_symm,
    from hT.left.right,
  unfold myset.image,
  existsi S.compl,
  split,
    split,
      from hS.left,
    rw myset.compl_subset_compl,
    from hS.right,
  rw myset.compl_compl,
end

theorem closure_minimal_closed_superset
(X: topological_space α) (A B: myset α):
X.is_closed B → A ⊆ B → X.closure A ⊆ B :=
begin
  assume hBcl hAB,
  intro x,
  assume hxAcl,
  from hxAcl B ⟨hBcl, hAB⟩,
end

theorem interior_maximal_open_subset
(X: topological_space α) (U V: myset α):
X.is_open V → V ⊆ U → V ⊆ X.interior U :=
begin
  assume hVo hVU,
  intro x,
  assume hVint,
  existsi V,
  split, {
    split; assumption,
  }, {
    assumption,
  },
end

theorem self_subset_closure
(X: topological_space α) (A: myset α):
A ⊆ X.closure A :=
begin
  intro a,
  assume hAa,
  intro F,
  assume hF,
  apply hF.right,
  assumption,
end

theorem interior_subset_self
(X: topological_space α) (U: myset α):
X.interior U ⊆ U :=
begin
  intro u,
  assume hUu,
  cases hUu with V hV,
  cases hV with hV huV,
  apply hV.right,
  assumption,
end

theorem closure_of_closed
(X: topological_space α) (A: myset α) (hAc: X.is_closed A):
X.closure A = A :=
begin
  apply myset.setext,
  intro x,
  split, {
    apply closure_minimal_closed_superset, {
      assumption,
    }, {
      refl,
    },
  }, {
    apply self_subset_closure _ A,
  },
end

theorem interior_of_open
(X: topological_space α) (U: myset α) (hUo: X.is_open U):
X.interior U = U :=
begin
  apply myset.setext,
  intro x,
  split, {
    apply interior_subset_self,
  }, {
    apply interior_maximal_open_subset _ _ U, {
      assumption,
    }, {
      refl,
    },
  },
end

theorem closure_idem_iff_closed
(X: topological_space α) (A: myset α):
X.closure A = A ↔ X.is_closed A :=
begin
  split, {
    assume h,
    rw ←h,
    apply closure_closed,
  }, {
    assume h,
    apply closure_of_closed,
    assumption,
  },
end

theorem interior_idem_iff_open
(X: topological_space α) (U: myset α):
X.interior U = U ↔ X.is_open U :=
begin
  split, {
    assume h,
    rw ←h,
    apply interior_open,
  }, {
    assume h,
    apply interior_of_open,
    assumption,
  },
end

theorem closure_subset
(X: topological_space α) (A B: myset α)
(hAB: A ⊆ B):
X.closure A ⊆ X.closure B :=
begin
  apply closure_minimal_closed_superset X A (X.closure B), {
    apply closure_closed,
  }, {
    apply myset.subset_trans A B (X.closure B), assumption,
    apply self_subset_closure,
  },
end

theorem interior_subset
(X: topological_space α) (U V: myset α)
(hUV: U ⊆ V):
X.interior U ⊆ X.interior V :=
begin
  apply interior_maximal_open_subset, {
    apply interior_open,
  }, {
    transitivity U, {
      apply interior_subset_self,
    }, {
      assumption,
    },
  },
end

theorem union_two_open
(X: topological_space α) (U V: myset α)
(hUo: X.is_open U) (hVo: X.is_open V):
X.is_open (U ∪ V) :=
begin
  rw myset.union_two_sUnion,
  apply X.open_union_open,
  intro S,
  assume hUVS,
  cases hUVS with h h; rw h; assumption,
end

theorem intersect_two_closed
(X: topological_space α) (U V: myset α)
(hUo: X.is_closed U) (hVo: X.is_closed V):
X.is_closed (U ∩ V) :=
begin
  unfold is_closed,
  -- should move into myset really
  have: (U ∩ V).compl = U.compl ∪ V.compl, {
    apply myset.setext,
    intro x,
    apply decidable.not_and_iff_or_not,
  },
  rw this,
  apply union_two_open; assumption,
end

-- if A ⊆ B is closed and B ⊆ C is closed,
-- then A is closed in C. yuckkkkkkkkkk
theorem closed_in_closed
(X: topological_space α) (U: myset α)
(hUcl: X.is_closed U)
(V: myset (subtype U))
(hVcl: (subspace_topology X U).is_closed V):
X.is_closed (myset.subtype_unrestriction U V) :=
begin
  cases hVcl with V' hV',
  cases hV' with hV'o hV',
  unfold myset.subtype_restriction at hV',
  have: (U.subtype_unrestriction V) = U ∩ V'.compl, {
    apply myset.setext,
    intro x,
    split, {
      assume hx,
      cases hx with hx hxV,
      split, {
        assumption,
      }, {
        assume hV'x,
        suffices hcontr: (⟨x, hx⟩: subtype U) ∈ V.compl, {
          contradiction,
        }, {
          rw hV',
          from hV'x,
        },
      },
    }, {
      assume hx,
      existsi hx.left,
      have: V.compl.compl = {w : subtype U | ↑w ∈ V'.compl}, {
        rw hV',
        refl,
      },
      rw myset.compl_compl at this,
      rw this,
      from hx.right,
    },
  },
  rw this,
  apply X.intersect_two_closed, {
    assumption,
  }, {
    unfold is_closed,
    rw myset.compl_compl,
    assumption,
  },
end

theorem closed_union_closed
(X: topological_space α) (U V: myset α)
(hUo: X.is_closed U) (hVo: X.is_closed V):
X.is_closed (U ∪ V) :=
begin
  unfold is_closed,
  have: (U ∪ V).compl = U.compl ∩ V.compl, {
    apply myset.setext,
    intro x,
    apply decidable.not_or_iff_and_not,
  },
  rw this,
  apply X.open_intersection_open; assumption,
end

theorem closed_intersection_closed
(X: topological_space α) (σ: myset (myset α))
(hSc: σ ⊆ X.is_closed):
X.is_closed ⋂₀ σ :=
begin
  rw ←myset.compl_compl (⋂₀σ),
  rw myset.compl_sIntersection,
  unfold is_closed,
  rw myset.compl_compl,
  apply open_union_open,
  intros S hS,
  unfold myset.image at hS,
  cases hS with T hT,
  rw hT.right.symm,
  from hSc _ hT.left,
end

-- finite intersections of open set are open,
-- stated with lists
theorem finite_open_intersection_open
(X: topological_space α) (σ : mylist (myset α))
(hso: mylist.for_all X.is_open σ):
X.is_open (mylist.reduce_d myset.intersection myset.univ σ) :=
begin
  induction σ, {
    from X.univ_open,
  }, {
    apply X.open_intersection_open, {
      from hso.left,
    }, {
      apply σ_ih,
      from hso.right,
    },
  },
end

theorem topological_space_eq:
∀ (X: topological_space α) (Y: topological_space α),
X.is_open = Y.is_open → X = Y
| ⟨Xo, _, _, _, _⟩ ⟨Yo, _, _, _, _⟩ rfl := rfl

theorem closure_intersects_all_open
(X: topological_space α) (A: myset α):
X.closure A =
{x : α | ∀ U: myset α, X.is_open U → x ∈ U → U ∩ A ≠ ∅} :=
begin
  apply myset.setext,
  intro x,
  split; assume hx, {
    intro U,
    assume hUo,
    assume hxU,
    assume hUAdisj,
    suffices h: x ∈ X.closure A ∩ U.compl, {
      from h.right hxU,
    }, {
      apply hx,
      split, {
        apply intersect_two_closed, {
          from closure_closed _ _,
        }, {
          unfold is_closed,
          rw myset.compl_compl,
          assumption,
        },
      }, {
        intro a,
        assume haA,
        split, {
          intro A',
          assume hA',
          apply hA'.right,
          assumption,
        }, {
          assume hUa,
          have: a ∈ U ∩ A, {
            split; assumption,
          },
          rw hUAdisj at this,
          from this,
        },
      },
    },
  }, {
    intro A',
    assume hA',
    by_contradiction h,
    suffices hcontr: A'.compl ∩ A ≠ ∅, {
      apply hcontr,
      apply myset.setext,
      intro x,
      split; assume hAx, {
        cases hAx with hA'x hAx,
        have := hA'.right x hAx,
        contradiction,
      }, {
        exfalso, from hAx,
      },
    },
    apply hx, {
      from hA'.left,
    }, {
      from h,
    },
  },
end

def is_dense (X : topological_space α) (A: myset α): Prop :=
closure X A = myset.univ

structure is_open_enclosure
(X: topological_space α) (U: myset α) (x: α)
(V: myset α): Prop :=
(is_open: X.is_open V)
(contains: x ∈ V)
(is_subset: V ⊆ U)

def is_neighbourhood (X: topological_space α) (U: myset α) (x: α): Prop :=
∃ V: myset α, is_open_enclosure X U x V

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
    }, {
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
      apply myset.setext,
      intro x,
      split; assume h, {
        cases h with V hV,
        cases hV with hV hxV,
        apply hV.right,
        assumption,
      }, {
        cases hUnbhd x h with V hV,
        existsi V,
        split, split, {
          from hV.is_open,
        }, {
          from hV.is_subset,
        }, {
          from hV.contains,
        },
      },
    },
  },
end

theorem basis_set_open
(B: myset (myset α)) (hB: is_base B) (U: myset α) (hUB: U ∈ B):
(space_from_base B hB).is_open U :=
begin
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
end

theorem hausdorff_iff_diagonal_closed
(X: topological_space α):
is_hausdorff X ↔ (product_topology X X).is_closed (λ xy, xy.fst = xy.snd) :=
begin
  split, {
    assume haus,
    unfold is_closed,
    rw open_iff_neighbourhood_forall,
    intro xy,
    assume hxydiag,
    have := haus xy.fst xy.snd hxydiag,
    cases this with U hUV,
    cases hUV with V hUV,
    existsi U × V,
    split, {
      apply basis_set_open,
      existsi U,
      existsi V,
      split, {
        refl,
      }, {
        from hUV.open_left,
      }, {
        from hUV.open_right,
      },
    }, {
      split, {
        from hUV.contains_left,
      }, {
        from hUV.contains_right,
      },
    }, {
      intro uv,
      assume huvUV,
      assume huvint,
      have := hUV.disjoint,
      rw ←myset.empty_iff_eq_empty at this,
      apply this uv.fst,
      split, {
        from huvUV.left,
      }, {
        change uv.fst = uv.snd at huvint,
        rw huvint,
        from huvUV.right,
      },
    },
  }, {
    assume hdiag,
    intros x y,
    assume hxy,
    cases hdiag ⟨x, y⟩ hxy with W hW,
    cases hW with hWpr hW,
    cases hWpr with U hUV,
    cases hUV with V hUV,
    existsi U,
    existsi V,
    rw hUV.eq at hW,
    split, {
      from hUV.open_left,
    }, {
      from hUV.open_right,
    }, {
      from hW.left.left,
    }, {
      from hW.left.right,
    }, {
      rw ←myset.empty_iff_eq_empty,
      intro uv,
      assume huv,
      apply hW.right ⟨uv, uv⟩, {
        from huv,
      }, {
        from rfl,
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
    from hUV.open_left,
  }, {
    from hUV.contains_left,
  }, {
    intro z,
    assume hUz,
    assume hzx,
    have := hUV.disjoint,
    rw ←myset.empty_iff_eq_empty at this,
    apply this x,
    split, {
      have: z = x := hzx,
      rw ←this,
      assumption,
    }, {
      from hUV.contains_right,
    },
  },
end

theorem discrete_subspace
(S: myset α):
discrete_topology (subtype S) =
subspace_topology (discrete_topology α) S :=
begin
  apply topological_space_eq,
  apply myset.setext,
  intro X,
  split; assume h, {
    existsi myset.subtype_unrestriction S X,
    split, {
      trivial,
    }, {
      apply myset.setext,
      intro x,
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
  apply myset.setext,
  intro X,
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

theorem empty_discrete (X: topological_space α):
discrete_topology (subtype (∅: myset α)) =
subspace_topology X ∅ :=
begin
  apply topological_space_eq,
  apply myset.setext,
  intro U,
  split; {
    assume hUo,
    have: U = ∅, {
      apply myset.setext,
      intro x,
      split; assume h, {
        exfalso, from x.property,
      }, {
        exfalso, from h,
      },
    },
    rw this,
    apply topological_space.empty_open,
  },
end

-- lol same proof
theorem empty_indiscrete (X: topological_space α):
indiscrete_topology (subtype (∅: myset α)) =
subspace_topology X ∅ :=
begin
  apply topological_space_eq,
  apply myset.setext,
  intro U,
  split; {
    assume hUo,
    have: U = ∅, {
      apply myset.setext,
      intro x,
      split; assume h, {
        exfalso, from x.property,
      }, {
        exfalso, from h,
      },
    },
    rw this,
    apply topological_space.empty_open,
  },
end

theorem singleton_indiscrete (X: topological_space α) (x: α):
indiscrete_topology (subtype (myset.singleton x)) =
subspace_topology X (myset.singleton x) :=
begin
  apply topological_space_eq,
  apply myset.setext,
  intro S,
  by_cases hSe: S = ∅, {
    rw hSe,
    split; assume h,
    from topological_space.empty_open _,
    from topological_space.empty_open _,
  }, {
    change S ≠ ∅ at hSe,
    rw ←myset.exists_iff_neq_empty at hSe,
    cases hSe with y hy,
    have: S = myset.univ, {
      apply myset.setext,
      intro z,
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
    from topological_space.univ_open _,
    from topological_space.univ_open _,
  },
end

theorem singleton_discrete (X: topological_space α) (x: α):
discrete_topology (subtype (myset.singleton x)) =
subspace_topology X (myset.singleton x) :=
begin
  apply topological_space_eq,
  apply myset.setext,
  intro S,
  by_cases hSe: S = ∅, {
    rw hSe,
    split; assume h,
    from topological_space.empty_open _,
    from topological_space.empty_open _,
  }, {
    change S ≠ ∅ at hSe,
    rw ←myset.exists_iff_neq_empty at hSe,
    cases hSe with y hy,
    have: S = myset.univ, {
      apply myset.setext,
      intro z,
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
    from topological_space.univ_open _,
    from topological_space.univ_open _,
  },
end

theorem hausdorff_subspace
(X: topological_space α)
(h_ausdorff: is_hausdorff X)
(Y: myset α):
is_hausdorff (X.subspace_topology Y) :=
begin
  intros x y,
  assume hxney,
  have := h_ausdorff x.val y.val
    begin
      assume hxy,
      apply hxney,
      apply subtype.eq,
      assumption,
    end,
  cases this with U hUV,
  cases hUV with V hUV,
  existsi Y.subtype_restriction U,
  existsi Y.subtype_restriction V,
  split, {
    existsi U,
    split, {
      from hUV.open_left,
    }, {
      refl,
    },
  }, {
    existsi V,
    split, {
      from hUV.open_right,
    }, {
      refl,
    },
  }, {
    from hUV.contains_left,
  }, {
    from hUV.contains_right,
  }, {
    rw ←myset.empty_iff_eq_empty,
    intro z,
    assume hz,
    apply myset.empty_iff_eq_empty.mpr hUV.disjoint z.val,
    split, {
      from hz.left,
    }, {
      from hz.right,
    },
  },
end

end topological_space
end hidden
