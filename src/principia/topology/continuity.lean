import .topological_space

namespace hidden

namespace topological_space

variables {α β γ: Type}

open classical

local attribute [instance] classical.prop_decidable

-- Goal Of The Game: sort out the [topological_space] arguments
-- just make it all ()

def is_continuous (f : α → β) [X : topological_space α] [Y : topological_space β] : Prop :=
∀ V : myset β, is_open Y V → is_open X (myset.inverse_image f V)

def is_open_map (X: topological_space α) (Y: topological_space β) (f: α → β): Prop :=
∀ U: myset α, is_open X U → is_open Y (myset.image f U)

-- is this right ???
structure is_homeomorphism
(X: topological_space α) (Y: topological_space β)
(f: α → β) (g: β → α): Prop :=
(f_continuous: @is_continuous _ _ f X Y)
(g_continuous: @is_continuous _ _ g Y X)
(right_inv: f ∘ g = id)
(left_inv: g ∘ f = id)

def homeomorphic (X: topological_space α) (Y: topological_space β): Prop :=
∃ (f: α → β) (g: β → α),
is_homeomorphism X Y f g

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

theorem swap_continuous
[X : topological_space α] [Y: topological_space β]:
@is_continuous (α × β) (β × α) (λ x, (x.snd, x.fst))
 (product_topology X Y) (product_topology Y X) :=
begin
  rw base_continuous,
  intro W,
  assume hWb,
  intro x,
  assume hx,
  cases hWb with U hWb,
  cases hWb with V hWVU,
  existsi V × U,
  split, {
    existsi V,
    existsi U,
    split, refl,
    split, from hWVU.right.right,
    from hWVU.right.left,
  }, split, {
    rw hWVU.left at hx,
    from and.comm.mp hx,
  }, {
    intro y,
    assume hy,
    rw hWVU.left,
    from and.comm.mp hy,
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

theorem homeomorphism_symm
(X: topological_space α) (Y: topological_space β)
(f: α → β) (g: β → α) (h_omeom: is_homeomorphism X Y f g):
is_homeomorphism Y X g f :=
begin
  cases h_omeom,
  split; assumption,
end

theorem homeomorphism_open
(X: topological_space α) (Y: topological_space β)
(f: α → β) (g: β → α) (h_omeom: is_homeomorphism X Y f g):
is_open_map X Y f :=
begin
  intro U,
  assume hUo,
  -- candidate for myset theorem?
  have: myset.image f U = myset.inverse_image g U, {
    apply funext,
    intro x,
    apply propext,
    split; assume h, {
      cases h with y hy,
      cases hy with hyU hxfy,
      rw ←hxfy,
      change id y ∈ U at hyU,
      rw ←h_omeom.left_inv at hyU,
      from hyU,
    }, {
      existsi g x,
      split, {
        from h,
      }, {
        change (f ∘ g) x = x,
        rw h_omeom.right_inv,
        refl,
      },
    },
  },
  rw this,
  apply h_omeom.g_continuous,
  assumption,
end

theorem swap_homeomorphism
(X : topological_space α) (Y: topological_space β):
is_homeomorphism (product_topology X Y) (product_topology Y X)
  (λ x, (x.snd, x.fst))
  (λ x', (x'.snd, x'.fst)) :=
begin
  split, {
    apply swap_continuous,
  }, {
    apply swap_continuous,
  }, {
    apply funext,
    intro x,
    cases x,
    refl,
  }, {
    apply funext,
    intro x',
    cases x',
    refl,
  },
end

theorem composition_open
(X: topological_space α) (Y: topological_space β) (Z: topological_space γ)
(f: α → β) (g: β → γ) (hfo: is_open_map X Y f) (hgo: is_open_map Y Z g):
is_open_map X Z (g ∘ f) :=
begin
  intro U,
  assume hUo,
  rw myset.image_composition,
  apply hgo,
  apply hfo,
  assumption,
end

theorem base_open
(B : myset (myset α)) (hB: is_base B)
(Y: topological_space β) (f: α → β):
is_open_map (space_from_base B hB) Y f ↔
(∀ W: myset α, W ∈ B → Y.is_open (myset.image f W)) :=
begin
  split; assume h, {
    intro W,
    assume hWB,
    apply h,
    -- maybe general theorem that basis sets are open
    intro x,
    assume hxW,
    existsi W,
    split, {
      assumption,
    }, split, {
      assumption,
    }, {
      refl,
    },
  }, {
    intro U,
    assume hUo,
    rw open_iff_neighbourhood_forall,
    intro x,
    assume hximf,
    cases hximf with y hy,
    cases hUo y hy.left with V hV,
    existsi (myset.image f V),
    split, {
      apply h,
      from hV.left,
    }, split, {
      existsi y,
      split, {
        from hV.right.left,
      }, {
        from hy.right,
      },
    }, {
      apply myset.image_subset,
      from hV.right.right,
    },
  },
end

theorem projection_open
(X : topological_space α) (Y: topological_space β):
is_open_map (product_topology X Y) X prod.fst :=
begin
  unfold product_topology,
  rw base_open,
  intro W,
  assume hWB,
  cases hWB with U hWB,
  cases hWB with V hWUV,
  -- so we don't have to worry about V being empty or not
  rw open_iff_neighbourhood_forall,
  intro x,
  assume hxW,
  existsi U,
  split, {
    from hWUV.right.left,
  }, split, {
    cases hxW with y hy,
    rw ←hy.right,
    rw hWUV.left at hy,
    from hy.left.left,
  }, {
    intro y,
    assume hUy,
    rw hWUV.left,
    cases hxW with z hz,
    existsi (⟨y, z.snd⟩: α × β),
    split, {
      split, {
        from hUy,
      }, {
        rw hWUV.left at hz,
        from hz.left.right,
      },
    }, {
      refl,
    },
  },
end

theorem projection_2_open
(X : topological_space α) (Y: topological_space β):
is_open_map (product_topology X Y) Y prod.snd :=
begin
  have :=
    composition_open
      (product_topology X Y) (product_topology Y X)
      Y (λ x: α × β, ⟨x.snd, x.fst⟩) prod.fst
      (homeomorphism_open _ _ _ _
        (swap_homeomorphism _ _))
      (projection_open _ _),
  have hrw: (prod.fst ∘ λ (x : α × β), (x.snd, x.fst)) = prod.snd, {
    apply funext,
    intro x,
    refl,
  },
  rw ←hrw,
  assumption,
end

theorem to_indiscrete_continuous (X: topological_space α) (f: α → β):
@is_continuous _ _  f X (indiscrete_topology β) :=
begin
  intro U,
  assume hUo,
  cases hUo with hU hU; rw hU, {
    from X.empty_open,
  }, {
    from X.univ_open,
  },
end

theorem to_discrete_open (X: topological_space α) (f: α → β):
is_open_map X (discrete_topology β) f :=
begin
  intro U,
  assume hUo,
  trivial,
end

theorem from_discrete_continuous (Y: topological_space β) (f: α → β):
@is_continuous _ _  f (discrete_topology α) Y :=
begin
  intro U,
  assume hUo,
  trivial,
end

theorem from_indiscrete_open_to_image (Y: topological_space β) (f: α → β):
is_open_map (indiscrete_topology α) (subspace_topology Y (myset.image f myset.univ))
  (myset.function_restrict_to_image f) :=
begin
  intro U,
  assume hUo,
  cases hUo with hU hU, {
    rw hU,
    -- weird function signature, probably my fault
    rw myset.image_empty (myset.function_restrict_to_image f) ∅ rfl,
    apply topological_space.empty_open,
  }, {
    rw hU,
    rw myset.to_image_surjective,
    apply topological_space.univ_open,
  },
end

end topological_space

end hidden
