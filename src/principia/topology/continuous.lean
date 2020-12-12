import .topological_space

namespace hidden

namespace topological_space

variables {α β γ: Type}

open classical

local attribute [instance] classical.prop_decidable

def is_continuous (f : α → β) [X : topological_space α] [Y : topological_space β] : Prop :=
∀ V : myset β, is_open Y V → is_open X (myset.inverse_image f V)

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

theorem continuous_to_image
[X : topological_space α] [Y : topological_space β]
(f: α → β):
@is_continuous _ _ f X Y →
@is_continuous _ _ (myset.function_restrict_to_image f)
               X (subspace_topology Y (myset.image f myset.univ)) :=
begin
  assume hfc,
  intro U,
  assume hUo,
  cases hUo with V hV,
  cases hV with hVo hVU,
  have: (myset.inverse_image (myset.function_restrict_to_image f) U)
        = myset.inverse_image f V, {
    apply funext,
    intro x,
    apply propext,
    split; assume h, {
      rw hVU at h,
      from h,
    }, {
      rw hVU,
      from h,
    },
  },
  rw this,
  from hfc V hVo,
end

theorem composition_continuous
[X : topological_space α] [Y : topological_space β]
[Z: topological_space γ]
(f: α → β) (g: β → γ)
(hfc: @is_continuous _ _ f X Y)
(hgc: @is_continuous _ _ g Y Z):
@is_continuous _ _ (g ∘ f) X Z :=
begin
  intro U,
  assume hUo,
  rw myset.inverse_image_composition,
  apply hfc,
  apply hgc,
  assumption,
end

theorem restriction_continuous
[X : topological_space α] [Y: topological_space β] (X': myset α)
(f: α → β) (hfc: @is_continuous _ _ f X Y):
@is_continuous (subtype X') _ (λ x, f x) (subspace_topology X X') Y :=
begin
  have: ((λ x, f x): (subtype X') → β) = f ∘ ((λ x, x): (subtype X' → α)), {
    apply funext,
    intro x,
    refl,
  },
  rw this,
  from @composition_continuous _ _ _ (subspace_topology X X') X Y _ f
    (@inclusion_continuous _ X X') hfc,
end

theorem projection_continuous
[X : topological_space α] [Y: topological_space β]:
@is_continuous _ _ prod.fst (product_topology X Y) X :=
begin
  intro U,
  assume hUo,
  intro x,
  assume hx,
  existsi U × myset.univ,
  split, {
    existsi U,
    existsi myset.univ,
    split, {
      refl,
    }, split, {
      assumption,
    }, {
      from Y.univ_open,
    },
  }, split, {
    split, {
      from hx,
    }, {
      trivial,
    },
  }, {
    intro y,
    assume hy,
    from hy.left,
  },
end

-- a bit less mind-numbing than unironically also proving it for snd
theorem swap_continuous
[X : topological_space α] [Y: topological_space β]:
@is_continuous (α × β) (β × α) (λ x, (x.snd, x.fst))
 (product_topology X Y) (product_topology Y X) :=
begin
  intro U,
  assume hUo,
  intro x,
  assume hx,
  cases hUo (x.snd, x.fst) hx with V hV,
  cases hV with hbox hV,
  cases hbox with Vv hbox,
  cases hbox with Vu hbox,
  existsi Vu × Vv,
  split, {
    existsi Vu,
    existsi Vv,
    split, {
      refl,
    }, {
      split, {
        from hbox.right.right,
      }, {
        from hbox.right.left,
      },
    },
  }, split, {
    rw hbox.left at hV,
    split, {
      from hV.left.right,
    }, {
      from hV.left.left,
    },
  }, {
    intro x',
    assume hx',
    apply hV.right,
    rw hbox.left,
    split, {
      from hx'.right,
    }, {
      from hx'.left,
    },
  },
end

theorem projection_2_continuous
[X : topological_space α] [Y: topological_space β]:
@is_continuous _ _ prod.snd (product_topology X Y) Y :=
begin
  have: (prod.snd: α × β → β) = prod.fst ∘ (λ x, (x.snd, x.fst)), {
    apply funext,
    intro x,
    refl,
  },
  rw this,
  apply @composition_continuous _ _ _ (product_topology X Y) (product_topology Y X) Y,
  from @swap_continuous _ _ X Y,
  from @projection_continuous _ _ Y X,
end

theorem base_continuous
[X: topological_space α]
(B : myset (myset β)) (hB : is_base B)
(f: α → β):
@is_continuous _ _ f X (space_from_base B hB) ↔
(∀ W: myset β, B W → X.is_open (myset.inverse_image f W)) :=
begin
  split, {
    assume hcf,
    intro W,
    assume hWB,
    apply hcf,
    intro x,
    assume hxW,
    existsi W,
    split, {
      assumption,
    }, split, {
      assumption,
    }, {
      intro x,
      assume hWx,
      assumption,
    },
  }, {
    assume hWpre,
    intro U,
    assume hUo,
    have := X.open_union_open,
    rw open_iff_neighbourhood_forall,
    intro x,
    assume hxpreU,
    cases hUo (f x) hxpreU with V hV,
    existsi myset.inverse_image f V,
    split, {
      apply hWpre,
      from hV.left,
    }, split, {
      from hV.right.left,
    }, {
      intro x',
      assume hx',
      apply hV.right.right,
      assumption,
    },
  },
end

theorem continuous_iff_components_continuous
[X : topological_space α] [Y: topological_space β]
[Z: topological_space γ] (f: α → β × γ):
@is_continuous _ _ f X (product_topology Y Z) ↔
(@is_continuous _ _ (prod.fst ∘ f) X Y ∧
 @is_continuous _ _ (prod.snd ∘ f) X Z) :=
begin
  split, {
    assume hcf,
    split, {
      apply @composition_continuous _ _ _ X (product_topology Y Z) Y,
      assumption,
      from @projection_continuous _ _ Y Z,
    }, {
      apply @composition_continuous _ _ _ X (product_topology Y Z) Z,
      assumption,
      from @projection_2_continuous _ _ Y Z,
    },
  }, {
    assume hc,
    cases hc with hc1 hc2,
    rw base_continuous,
    intro W,
    assume hW,
    cases hW with U hW,
    cases hW with V hW,
    have: (myset.inverse_image f W)
        = myset.inverse_image (prod.fst ∘ f) U ∩
          myset.inverse_image (prod.snd ∘ f) V, {
      apply funext,
      intro x,
      apply propext,
      split; assume h, {
        split, {
          rw hW.left at h,
          from h.left,
        }, {
          rw hW.left at h,
          from h.right,
        },
      }, {
        rw hW.left,
        from h,
      },
    },
    rw this,
    apply X.open_intersection_open, {
      apply hc1,
      from hW.right.left,
    }, {
      apply hc2,
      from hW.right.right,
    },
  },
end

theorem continuous_iff_closed_preimage
(X: topological_space α) (Y: topological_space β)
(f: α → β):
@is_continuous _ _ f X Y ↔
(∀ V : myset β, Y.is_closed V → X.is_closed (myset.inverse_image f V)) :=
begin
  split, {
    assume hfc,
    intro V,
    assume hVcl,
    change X.is_open (myset.inverse_image f V.compl),
    apply hfc,
    from hVcl,
  }, {
    assume hfc',
    intro U,
    assume hUo,
    rw ←myset.compl_compl U,
    change X.is_closed (myset.inverse_image f U.compl),
    apply hfc',
    unfold is_closed,
    rw myset.compl_compl,
    assumption,
  },
end

theorem gluing_lemma
(X: topological_space α) (Y: topological_space β)
(U V: myset α) (hUc: X.is_closed U) (hVc: X.is_closed V)
(hUVcov: U ∪ V = myset.univ) (f: α → β):
@is_continuous (subtype U) _ (λ x, f x) (subspace_topology X U) Y →
@is_continuous (subtype V) _ (λ x, f x) (subspace_topology X V) Y →
@is_continuous _ _ f X Y :=
begin
  repeat {rw continuous_iff_closed_preimage},
  assume hfUc hfVc,
  intro W,
  assume hWcl,
  cases hfUc W hWcl with U' hU',
  cases hfVc W hWcl with V' hV',
  have:
      (myset.inverse_image f W) =
        (myset.subtype_unrestriction U
          (@myset.inverse_image (subtype U) _ (λ x, f x) W)) ∪
        (myset.subtype_unrestriction V
          (@myset.inverse_image (subtype V) _ (λ x, f x) W)), {
    apply funext,
    intro x,
    apply propext,
    split, {
      assume hfWx,
      have: x ∈ U ∪ V, {
        rw hUVcov,
        trivial,
      },
      cases this with hU hV, {
        left,
        existsi hU,
        from hfWx,
      }, {
        right,
        existsi hV,
        from hfWx,
      },
    }, {
      assume hUVx,
      cases hUVx with hU hV, {
        cases hU with hxU hU,
        from hU,
      }, {
        cases hV with hxV hV,
        from hV,
      },
    },
  },
  rw this,
  apply X.closed_union_closed, {
    apply closed_in_closed X U hUc,
    apply hfUc,
    assumption,
  }, {
    apply closed_in_closed X V hVc,
    apply hfVc,
    assumption,
  },
end


end topological_space

end hidden
