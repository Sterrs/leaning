import .topological_space

namespace hidden

namespace topological_space

variables {α β γ: Type}

open classical

local attribute [instance] classical.prop_decidable

def is_continuous
(X: topological_space α) (Y: topological_space β)
(f: α → β): Prop :=
∀ V : myset β, is_open Y V → is_open X (myset.inverse_image f V)

def is_open_map (X: topological_space α) (Y: topological_space β) (f: α → β): Prop :=
∀ U: myset α, is_open X U → is_open Y (myset.image f U)

-- is this right ???
structure is_homeomorphism
(X: topological_space α) (Y: topological_space β)
(f: α → β) (g: β → α): Prop :=
(f_continuous: is_continuous X Y f)
(g_continuous: is_continuous Y X g)
(right_inv: f ∘ g = id)
(left_inv: g ∘ f = id)

def homeomorphic (X: topological_space α) (Y: topological_space β): Prop :=
∃ (f: α → β) (g: β → α),
is_homeomorphism X Y f g

theorem identity_continuous (X : topological_space α):
is_continuous X X id :=
begin
  intro V,
  assume hoV,
  have: V = myset.inverse_image id V := rfl,
  rw ←this,
  assumption,
end

theorem constant_continuous
(X: topological_space α) (Y: topological_space β)
(y: β):
is_continuous X Y (λ x, y) :=
begin
  intro V,
  assume hoV,
  by_cases hy: y ∈ V, {
    have: (myset.inverse_image (λ (x : α), y) V) = myset.univ,  {
      apply myset.setext,
      intro x,
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
      apply myset.setext,
      intro x,
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
(X : topological_space α) (Y: myset α):
is_continuous (subspace_topology X Y) X subtype.val :=
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

theorem s_inclusion_continuous
(X: topological_space α)
(Y: myset α) (Z: myset α) (hYZ: Y ⊆ Z):
is_continuous
  (X.subspace_topology Y) (X.subspace_topology Z)
  (λ y, ⟨y.val, hYZ y y.property⟩) :=
begin
  intro U,
  assume hUo,
  cases hUo with V hV,
  existsi V,
  split, {
    from hV.left,
  }, {
    apply myset.setext,
    intro x,
    split; assume hx, {
      unfold myset.subtype_restriction,
      rw hV.right at hx,
      from hx,
    }, {
      rw hV.right,
      from hx,
    },
  },
end

theorem continuous_to_image
(X : topological_space α) (Y : topological_space β)
(f: α → β):
is_continuous X Y f →
is_continuous X (subspace_topology Y (myset.imageu f))
  (myset.function_restrict_to_image f) :=
begin
  assume hfc,
  intro U,
  assume hUo,
  cases hUo with V hV,
  cases hV with hVo hVU,
  have: (myset.inverse_image (myset.function_restrict_to_image f) U)
        = myset.inverse_image f V, {
    rw hVU,
    refl,
  },
  rw this,
  from hfc V hVo,
end

theorem composition_continuous
(X: topological_space α) (Y: topological_space β)
(Z: topological_space γ)
(f: α → β) (g: β → γ)
(hfc: is_continuous X Y f)
(hgc: is_continuous Y Z g):
is_continuous X Z (g ∘ f) :=
begin
  intro U,
  assume hUo,
  rw myset.inverse_image_composition,
  apply hfc,
  apply hgc,
  assumption,
end

theorem restriction_continuous
(X : topological_space α) (Y: topological_space β) (X': myset α)
(f: α → β) (hfc: is_continuous X Y f):
is_continuous (subspace_topology X X') Y (λ x, f x) :=
begin
  have: ((λ x, f x): (subtype X') → β) = f ∘ ((λ x, x): (subtype X' → α)), {
    apply funext,
    intro x,
    refl,
  },
  rw this,
  from composition_continuous (subspace_topology X X') X Y _ f
    (inclusion_continuous X X') hfc,
end

-- couldn't quite figure out if this is a composition
-- of things we already know about
theorem restrict_set_to_image_continuous
(X : topological_space α) (Y : topological_space β)
(f: α → β) (hfc: is_continuous X Y f) (U: myset α):
(X.subspace_topology U).is_continuous (Y.subspace_topology (myset.image f U))
    (myset.function_restrict_to_set_image f U) :=
begin
  intro V',
  assume hV'o,
  cases hV'o with V hV,
  existsi myset.inverse_image f V,
  split, {
    from hfc _ hV.left,
  }, {
    rw hV.right,
    refl, -- god bless america
  },
end

theorem base_continuous
(X: topological_space α)
(B : myset (myset β)) (hB : is_base B)
(f: α → β):
is_continuous X (space_from_base B hB) f ↔
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
    }, {
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
(X : topological_space α) (Y: topological_space β):
is_continuous (product_topology X Y) X prod.fst :=
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
    }, {
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
(X : topological_space α) (Y: topological_space β):
is_continuous (product_topology X Y) (product_topology Y X)
  (λ x, (x.snd, x.fst)) :=
begin
  unfold product_topology,
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
    from hWVU.open_right,
    from hWVU.open_left,
  }, split, {
    rw hWVU.eq at hx,
    from and.comm.mp hx,
  }, {
    intro y,
    assume hy,
    rw hWVU.eq,
    from and.comm.mp hy,
  },
end

theorem projection_2_continuous
(X : topological_space α) (Y: topological_space β):
is_continuous (product_topology X Y) Y prod.snd :=
begin
  have: (prod.snd: α × β → β) = prod.fst ∘ (λ x, (x.snd, x.fst)), {
    apply funext,
    intro x,
    refl,
  },
  rw this,
  apply composition_continuous (product_topology X Y) (product_topology Y X) Y,
  from swap_continuous X Y,
  from projection_continuous Y X,
end

theorem continuous_iff_components_continuous
(X : topological_space α) (Y: topological_space β)
(Z: topological_space γ) (f: α → β × γ):
is_continuous X (product_topology Y Z) f ↔
(is_continuous X Y (prod.fst ∘ f) ∧
 is_continuous X Z (prod.snd ∘ f)) :=
begin
  split, {
    assume hcf,
    split, {
      apply composition_continuous X (product_topology Y Z) Y,
      assumption,
      from projection_continuous Y Z,
    }, {
      apply composition_continuous X (product_topology Y Z) Z,
      assumption,
      from projection_2_continuous Y Z,
    },
  }, {
    assume hc,
    cases hc with hc1 hc2,
    unfold product_topology,
    rw base_continuous,
    intro W,
    assume hW,
    cases hW with U hW,
    cases hW with V hW,
    have: (myset.inverse_image f W)
        = myset.inverse_image (prod.fst ∘ f) U ∩
          myset.inverse_image (prod.snd ∘ f) V, {
      apply myset.setext,
      intro x,
      rw hW.eq,
      refl,
    },
    rw this,
    apply X.open_intersection_open, {
      apply hc1,
      from hW.open_left,
    }, {
      apply hc2,
      from hW.open_right,
    },
  },
end

theorem continuous_iff_closed_preimage
(X: topological_space α) (Y: topological_space β)
(f: α → β):
is_continuous X Y f ↔
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

-- question 8 from M&T sheet 1
theorem continuous_iff_closure_subset
(X: topological_space α) (Y: topological_space β)
(f: α → β):
is_continuous X Y f ↔
∀ A: myset α, myset.image f (X.closure A) ⊆ Y.closure (myset.image f A) :=
begin
  split, {
    assume hfc,
    intro A,
    -- transitivity myset.image f (myset.inverse_image f (Y.closure (myset.image f A))),
    -- wtf is its problem
    -- I think it has something to do with metavariables depending on each other
    apply myset.subset_trans _
        (myset.image f (myset.inverse_image f (Y.closure (myset.image f A))))
        (Y.closure (myset.image f A)), {
      apply myset.image_subset,
      -- should be inferable
      apply closure_minimal_closed_superset X A (myset.inverse_image f (Y.closure (myset.image f A))), {
        unfold closure,
        rw myset.inverse_image_sIntersection,
        apply closed_intersection_closed,
        intro B,
        assume hB,
        cases hB with B' hB',
        rw ←hB'.right,
        rw continuous_iff_closed_preimage at hfc,
        apply hfc,
        from hB'.left.left,
      }, {
        -- transitivity (myset.inverse_image f (myset.image f A)).
        apply myset.subset_trans _
            (myset.inverse_image f (myset.image f A))
            (myset.inverse_image f (Y.closure (myset.image f A))), {
          apply myset.inverse_image_of_image,
        }, {
          -- should be inferable
          apply myset.inverse_image_subset f (myset.image f A) ((Y.closure (myset.image f A))),
          apply self_subset_closure,
        },
      },
    }, {
      -- should be inferable
      apply myset.image_of_inverse_image f (Y.closure (myset.image f A)),
    },
  }, {
    assume hclosure_subset,
    rw continuous_iff_closed_preimage,
    intro A,
    assume hAc,
    rw ←closure_idem_iff_closed,
    apply myset.setext_subs, {
      transitivity myset.inverse_image f (myset.image f (X.closure (myset.inverse_image f A))), {
        apply myset.inverse_image_of_image,
      }, {
        apply myset.inverse_image_subset,
        apply myset.subset_trans _ _ A (hclosure_subset _),
        conv {
          to_rhs,
          rw ←(closure_idem_iff_closed Y A).mpr hAc,
        },
        apply closure_subset,
        apply myset.image_of_inverse_image,
      },
    }, {
      apply self_subset_closure,
    },
  },
end

theorem surjective_image_dense
(X: topological_space α) (Y: topological_space β)
(A: myset α) (hAd: X.is_dense A)
(f: α → β) (hfc: is_continuous X Y f)
(hsurj: function.surjective f):
Y.is_dense (myset.image f A) :=
begin
  apply myset.setext_subs, {
    from λ _ _, trivial,
  }, {
    intro y,
    assume hyt, clear hyt,
    apply (continuous_iff_closure_subset X Y f).mp hfc,
    unfold is_dense at hAd,
    rw hAd,
    cases hsurj y with x hx,
    rw ←hx,
    existsi x,
    split, {
      trivial,
    }, {
      refl,
    },
  },
end

theorem hausdorff_dense_determinism
(X: topological_space α) (Y: topological_space β)
(haus: is_hausdorff Y)
(A: myset α) (hAd: X.is_dense A)
(f g: α → β) (hfc: is_continuous X Y f) (hgc: is_continuous X Y g)
(hagree: ∀ a: α, a ∈ A → f a = g a):
f = g :=
begin
  have hagreecl: X.is_closed {x | f x = g x}, {
    have: is_continuous X (product_topology Y Y) (λ x, (f x, g x)), {
      rw continuous_iff_components_continuous,
      split, {
        from hfc,
      }, {
        from hgc,
      },
    },
    rw continuous_iff_closed_preimage at this,
    apply this {yy | yy.fst = yy.snd},
    rw hausdorff_iff_diagonal_closed at haus,
    from haus,
  },
  rw ←closure_idem_iff_closed at hagreecl,
  have heverywhere: {x : α | f x = g x} = myset.univ, {
    apply myset.setext_subs, {
      from λ _ _, trivial,
    }, {
      transitivity X.closure A, {
        unfold is_dense at hAd,
        rw hAd,
      }, {
        rw ←hagreecl,
        apply closure_subset,
        intro a,
        assume ha,
        from hagree a ha,
      },
    },
  },
  apply funext,
  intro x,
  change x ∈ {x : α | f x = g x},
  rw heverywhere,
  trivial,
end

theorem gluing_lemma
(X: topological_space α) (Y: topological_space β)
(U V: myset α) (hUc: X.is_closed U) (hVc: X.is_closed V)
(hUVcov: U ∪ V = myset.univ) (f: α → β):
is_continuous (subspace_topology X U) Y (λ x, f x) →
is_continuous (subspace_topology X V) Y (λ x, f x) →
is_continuous X Y f :=
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
    apply myset.setext,
    intro x,
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

theorem homeomorphism_refl
(X: topological_space α):
is_homeomorphism X X id id :=
begin
  split, {
    from identity_continuous X,
  }, {
    from identity_continuous X,
  }, {
    -- don't question it. I have no idea why this doesn't need
    -- extensionality
    refl,
  }, {
    refl,
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

theorem homeomorphism_trans
(X: topological_space α) (Y: topological_space β)
(Z: topological_space γ) (f: α → β) (g: β → α)
(f': β → γ) (g': γ → β)
(hfghom: is_homeomorphism X Y f g)
(hfg'hom: is_homeomorphism Y Z f' g'):
is_homeomorphism X Z (f' ∘ f) (g ∘ g') :=
begin
  cases hfghom,
  cases hfg'hom,
  split, {
    apply composition_continuous _ Y; assumption,
  }, {
    apply composition_continuous _ Y; assumption,
  }, {
    change f' ∘ (f ∘ g) ∘ g' = id,
    rw hfghom_right_inv,
    change f' ∘ g' = id,
    assumption,
  }, {
    change g ∘ (g' ∘ f') ∘ f = id,
    rw hfg'hom_left_inv,
    change g ∘ f = id,
    assumption,
  },
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
    apply myset.setext,
    intro x,
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
    apply basis_set_open,
    assumption,
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
    }, {
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
    from hWUV.open_left,
  }, {
    cases hxW with y hy,
    rw ←hy.right,
    rw hWUV.eq at hy,
    from hy.left.left,
  }, {
    intro y,
    assume hUy,
    rw hWUV.eq,
    cases hxW with z hz,
    existsi (⟨y, z.snd⟩: α × β),
    split, {
      split, {
        from hUy,
      }, {
        rw hWUV.eq at hz,
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
is_continuous X (indiscrete_topology β) f :=
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
is_continuous (discrete_topology α) Y f :=
begin
  intro U,
  assume hUo,
  trivial,
end

theorem from_indiscrete_open_to_image (Y: topological_space β) (f: α → β):
is_open_map (indiscrete_topology α) (subspace_topology Y (myset.imageu f))
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

theorem univ_homeomorphism
(X : topological_space α):
is_homeomorphism X (X.subspace_topology myset.univ)
  (λ x, ⟨x, trivial⟩) subtype.val :=
begin
  split, {
    -- is this a theorem already? idc anymore
    intro U,
    assume hUo,
    cases hUo with V hV,
    rw hV.right,
    from hV.left,
  }, {
    apply inclusion_continuous,
  }, {
    apply funext,
    intro x,
    apply subtype.eq,
    refl,
  }, {
    refl,
  },
end

end topological_space

end hidden
