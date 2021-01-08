import .topological_space
import .continuity

namespace hidden

namespace topological_space

variables {α β : Type}

open classical

local attribute [instance] classical.prop_decidable

-- Goal Of The Game: product of connected spaces is connected

def is_disconnected (X : topological_space α) : Prop :=
∃ U V : myset α, U ≠ ∅ ∧ V ≠ ∅ ∧ is_open X U ∧ is_open X V ∧ U ∩ V = ∅ ∧ U ∪ V = myset.univ

def is_connected (X : topological_space α) : Prop :=
¬is_disconnected X

theorem disconnect_clopen (X: topological_space α) (U V: myset α):
X.is_open U ∧ X.is_open V ∧ U ∩ V = ∅ ∧ U ∪ V = myset.univ →
X.is_closed U ∧ X.is_closed V :=
begin
  assume h,
  cases h with hUo h,
  cases h with hVo h,
  cases h with hUVdsj hUVcov,
  -- also a candidate for myset
  have: U.compl = V, {
    apply myset.setext,
    intro x,
    split, {
      assume hx,
      have: x ∈ U ∪ V, {
        rw hUVcov, trivial,
      },
      cases this with hU hV, {
        contradiction,
      }, {
        assumption,
      },
    }, {
      assume hx hUx,
      have: x ∈ U ∩ V, {
        split; assumption,
      },
      rw hUVdsj at this,
      from this,
    },
  },
  rw ←myset.compl_compl U,
  conv {
    congr,
    rw this,
    skip,
    rw ←this,
  },
  unfold is_closed,
  repeat {rw myset.compl_compl},
  split; assumption,
end

theorem surjective_image_connected
(X: topological_space α) (Y: topological_space β)
(f: α → β) (hfc: is_continuous X Y f) (hsurj: function.surjective f):
is_connected X → is_connected Y :=
begin
  assume hXc,
  assume himdc,
  cases himdc with U himdc,
  cases himdc with V himdc,
  cases himdc with hUne himdc,
  cases himdc with hVne himdc,
  cases himdc with hUo himdc,
  cases himdc with hVo himdc,
  cases himdc with hUVdj hUVcov,
  have hpreUo := hfc U hUo,
  have hpreVo := hfc V hVo,
  apply hXc,
  existsi (myset.inverse_image f U),
  existsi (myset.inverse_image f V),
  split, {
    assume hpreUe,
    rw ←myset.exists_iff_neq_empty at hUne,
    rw ←myset.empty_iff_eq_empty at hpreUe,
    cases hUne with y hy,
    cases hsurj y with x hx,
    apply hpreUe x,
    rw ←hx at hy,
    from hy,
  }, split, {
    assume hpreVe,
    rw ←myset.exists_iff_neq_empty at hVne,
    rw ←myset.empty_iff_eq_empty at hpreVe,
    cases hVne with y hy,
    cases hsurj y with x hx,
    apply hpreVe x,
    rw ←hx at hy,
    from hy,
  }, split, {
    from hfc U hUo,
  }, split, {
    from hfc V hVo,
  }, split, {
    rw ←myset.inverse_image_intersection,
    rw hUVdj,
    rw myset.inverse_image_empty,
    refl,
  }, {
    rw ←myset.inverse_image_union,
    rw hUVcov,
    have := myset.inverse_image_of_image_of_univ (myset.function_restrict_to_image f),
    rw myset.to_image_surjective at this,
    from this.symm,
  },
end

theorem image_connected
(X: topological_space α) (Y: topological_space β)
(f: α → β) (hfc: is_continuous X Y f)
(hconn: is_connected X):
is_connected (Y.subspace_topology (myset.imageu f)) :=
begin
  apply surjective_image_connected X _ (myset.function_restrict_to_image f), {
    apply continuous_to_image,
    from hfc,
  }, {
    intro y,
    cases y.property with x hx,
    existsi x,
    apply subtype.eq,
    from hx,
  }, {
    from hconn,
  }
end

theorem discrete_disconnected
(x y: α) (hxy: x ≠ y):
is_disconnected (discrete_topology α) :=
begin
  existsi {z | z = x},
  existsi {z | z ≠ x},
  split, {
    rw ←myset.exists_iff_neq_empty,
    existsi x,
    from rfl,
  }, split, {
    rw ←myset.exists_iff_neq_empty,
    existsi y,
    change ¬(x = y) at hxy,
    from λ h, hxy h.symm,
  }, split, {
    trivial,
  }, split, {
    trivial,
  }, split, {
    apply myset.setext,
    intro z,
    split; assume h, {
      cases h, contradiction,
    }, {
      exfalso, from h,
    },
  }, {
    apply myset.setext,
    intro z,
    split; assume h, {
      trivial,
    }, {
      apply decidable.em,
    },
  },
end

theorem indiscrete_connected:
is_connected (indiscrete_topology α) :=
begin
  assume hdc,
  cases hdc with U hdc,
  cases hdc with V hdc,
  cases hdc with hUne hdc,
  cases hdc with hVne hdc,
  cases hdc with hUo hdc,
  cases hdc with hVo hdc,
  cases hUo with hU hU, {
    contradiction,
  }, {
    cases hVo with hV hV, {
      contradiction,
    }, {
      rw ←myset.exists_iff_neq_empty at hUne,
      rw ←myset.exists_iff_neq_empty at hVne,
      cases hUne with x hxU,
      cases hVne with y hyU,
      cases hdc with hUVdj hUVcov,
      rw ←myset.empty_iff_eq_empty at hUVdj,
      apply hUVdj x,
      split, {
        assumption,
      }, {
        rw hV,
        trivial,
      },
    },
  },
end

theorem empty_connected
(X: topological_space α):
is_connected (subspace_topology X ∅) :=
begin
  rw ←empty_indiscrete,
  apply indiscrete_connected,
end

theorem singleton_connected
(X: topological_space α) (x: α):
is_connected (subspace_topology X (myset.singleton x)) :=
begin
  rw ←singleton_indiscrete,
  apply indiscrete_connected,
end

-- maybe split up more to avoid cpu stress
theorem connected_iff_N_image_const
(X: topological_space α):
is_connected X ↔
∀ f: α → mynat,
  is_continuous X (discrete_topology mynat) f →
  ∀ x y: α, f x = f y :=
begin
  split, {
    assume hXc,
    intro f,
    assume hfc,
    intros x y,
    by_contradiction hfxfy,
    apply hXc,
    existsi myset.inverse_image f {n | n = f x},
    existsi myset.inverse_image f ({n | n ≠ f x}),
    split, {
      rw ←myset.exists_iff_neq_empty,
      existsi x,
      from rfl,
    }, split, {
      rw ←myset.exists_iff_neq_empty,
      existsi y,
      assume h,
      from hfxfy h.symm,
    }, split, {
      apply hfc,
      trivial,
    }, split, {
      apply hfc,
      trivial,
    }, split, {
      rw ←myset.inverse_image_intersection,
      apply myset.inverse_image_empty,
      apply myset.setext,
      intro z,
      split, {
        assume h,
        cases h,
        contradiction,
      }, {
        assume h,
        exfalso, from h,
      },
    }, {
      apply myset.setext,
      intro z,
      split, {
        assume h, trivial,
      }, {
        assume h,
        apply decidable.em,
      },
    },
  }, {
    assume hfNc,
    assume hXdc,
    cases hXdc with U hXdc,
    cases hXdc with V hXdc,
    suffices:
        ∃ (f : α → mynat),
          is_continuous X (discrete_topology mynat) f ∧
          ∃ (x y : α), f x ≠ f y, {
      cases this with f hf,
      cases hf with hfc hxy,
      cases hxy with x hxy,
      cases hxy with y hxy,
      apply hxy,
      apply hfNc,
      assumption,
    }, {
      existsi (λ x, if x ∈ U then (0: mynat) else 1),
      split, {
        have := disconnect_clopen _ _ _ hXdc.right.right,
        apply gluing_lemma X _ U V, {
          from this.left,
        }, {
          from this.right,
        }, {
          from hXdc.right.right.right.right.right,
        }, {
          suffices
              hconst:
              (λ (x : subtype U), ite (↑x ∈ U) (0: mynat) 1) =
              (λ x, 0), {
            rw hconst,
            apply constant_continuous,
          }, {
            apply funext,
            intro x,
            have hxU: (↑x ∈ U) := x.property,
            rw if_pos hxU,
          },
        }, {
          suffices
            hconst:
            (λ (x : subtype V), ite (↑x ∈ U) (0: mynat) 1) =
            (λ x, 1), {
            rw hconst,
            apply constant_continuous,
          }, {
            apply funext,
            intro x,
            have hxU: (↑x ∉ U), {
              assume hxU,
              have hUVx: ↑x ∈ U ∩ V, {
                split, {
                  assumption,
                }, {
                  from x.property,
                },
              },
              rw hXdc.right.right.right.right.left at hUVx,
              from hUVx,
            },
            rw if_neg hxU,
          },
        },
      }, {
        cases hXdc with hUne hXdc,
        cases hXdc with hVne hXdc,
        rw ←myset.exists_iff_neq_empty at hUne,
        rw ←myset.exists_iff_neq_empty at hVne,
        cases hUne with x hx,
        cases hVne with y hy,
        existsi x,
        existsi y,
        simp,
        rw if_pos hx,
        have hyU: y ∉ U, {
          assume hyU,
          have: y ∈ U ∩ V, {
            split; assumption,
          },
          rw hXdc.right.right.left at this,
          from this,
        },
        rw if_neg hyU,
        from mynat.zero_ne_one,
      },
    },
  },
end

-- so it gets it from the other equality for you
private lemma transitivity' {α: Type} {x y z w: α}:
y = z → x = y → z = w → x = w :=
begin
  assume hyz hxy hzw,
  transitivity z,
  transitivity y,
  all_goals {assumption},
end

-- does this even end up being faster (:
theorem s_union_of_overlapping_connected
(X: topological_space α)
(S: myset (myset α))
(hconn: ∀ U: myset α, U ∈ S →
 is_connected (subspace_topology X U))
(hlap: ∀ U V: myset α,
 U ∈ S → V ∈ S → U ∩ V ≠ ∅):
is_connected (subspace_topology X (⋃₀ S)) :=
begin
  rw connected_iff_N_image_const,
  intro f,
  assume hfc,
  intros x y,
  cases x.property with U hU,
  cases hU with hU hxU,
  cases y.property with V hV,
  cases hV with hV hxV,
  have hUVdsj := hlap U V hU hV,
  rw ←myset.exists_iff_neq_empty at hUVdsj,
  cases hUVdsj with z hz,
  have hUcon := hconn U hU,
  have hVcon := hconn V hV,
  rw connected_iff_N_image_const at hUcon,
  rw connected_iff_N_image_const at hVcon,
  transitivity f (⟨z, ⟨U, ⟨hU, hz.left⟩⟩⟩: subtype (⋃₀ S)), {
    have step1 := hUcon (λ x: subtype U, f ⟨x, ⟨U, ⟨hU, x.property⟩⟩⟩),
    let g := (λ x: subtype U, f ⟨x, ⟨U, ⟨hU, x.property⟩⟩⟩),
    have h_elp_me:
        is_continuous (subspace_topology X U) (discrete_topology mynat) g, {
      apply
          composition_continuous
            (subspace_topology X U) (X.subspace_topology (⋃₀ S))
            (discrete_topology mynat), {
        have: U ⊆ ⋃₀ S, {
          intro u,
          assume hUu,
          existsi U,
          from ⟨hU, hUu⟩,
        },
        apply s_inclusion_continuous X U (⋃₀ S) this,
      }, {
        from hfc,
      },
    },
    have step2 := step1 h_elp_me ⟨x.val, hxU⟩ ⟨z, hz.left⟩,
    apply transitivity' step2, {
      congr,
      apply subtype.eq,
      refl,
    }, {
      from rfl,
    },
  }, {
    symmetry,
    have step1 := hVcon (λ x: subtype V, f ⟨x, ⟨V, ⟨hV, x.property⟩⟩⟩),
    let g := (λ x: subtype V, f ⟨x, ⟨V, ⟨hV, x.property⟩⟩⟩),
    have h_elp_me:
        is_continuous (subspace_topology X V) (discrete_topology mynat) g, {
      apply
          composition_continuous
            (subspace_topology X V) (X.subspace_topology (⋃₀ S))
            (discrete_topology mynat), {
        have: V ⊆ ⋃₀ S, {
          intro v,
          assume hVv,
          existsi V,
          from ⟨hV, hVv⟩,
        },
        apply s_inclusion_continuous X V (⋃₀ S) this,
      }, {
        from hfc,
      },
    },
    have step2 := step1 h_elp_me ⟨y.val, hxV⟩ ⟨z, hz.right⟩,
    apply transitivity' step2, {
      congr,
      apply subtype.eq,
      refl,
    }, {
      from rfl,
    },
  },
end

theorem union_of_two_overlapping_connected
(X: topological_space α)
(U V: myset α)
(hUcn: is_connected (X.subspace_topology U))
(hVcn: is_connected (X.subspace_topology V))
(hlap: U ∩ V ≠ ∅):
is_connected (subspace_topology X (U ∪ V)) :=
begin
  rw myset.union_two_sUnion,
  apply s_union_of_overlapping_connected, {
    intro W,
    assume hW,
    cases hW; {rw hW, assumption},
  }, {
    intros W1 W2,
    assume hW1 hW2,
    rw ←myset.exists_iff_neq_empty at hlap ⊢,
    cases hlap with x hx,
    existsi x,
    cases hx with hUx hVx,
    split, {
      cases hW1; {rw hW1, assumption},
    }, {
      cases hW2; {rw hW2, assumption},
    },
  },
end

private lemma line_connected
(X: topological_space α) (Y: topological_space β)
(hYcn: is_connected Y) (x: α):
is_connected ((product_topology X Y).subspace_topology
  {xy | xy.fst = x}) :=
begin
  have: {xy : α × β | xy.fst = x}
      = myset.imageu (λ y: β, (x, y)), {
    apply myset.setext,
    intro z,
    split; assume hx, {
      existsi z.snd,
      cases z,
      apply congr,
      apply congr_arg prod.mk,
      from hx.symm,
      refl,
    }, {
      cases hx with y hy,
      rw ←hy,
      from rfl,
    },
  },
  rw this, clear this,
  apply image_connected Y _ (λ (y : β), (x, y)), {
    rw continuous_iff_components_continuous,
    split, {
      apply constant_continuous _ _ x,
    }, {
      apply identity_continuous,
    },
  }, {
    assumption,
  },
end

private lemma cross_connected
(X: topological_space α) (Y: topological_space β)
(hXcn: is_connected X) (hYcn: is_connected Y)
(x: α) (y: β):
is_connected
  ((product_topology X Y).subspace_topology
    (λ xy', xy'.fst = x ∨ xy'.snd = y)) :=
begin
  apply union_of_two_overlapping_connected, {
    apply line_connected,
    assumption,
  }, {
    have homeom := swap_homeomorphism X Y,
    have hlcn := line_connected Y X hXcn y,
    have himcn :=
        image_connected _ _ _
          (restriction_continuous _ _ _ _ homeom.g_continuous) hlcn,
    have:
        (λ a : α × β, a.snd = y)
        = myset.imageu
          (λ (x : subtype {xy : β × α | xy.fst = y}), (x.val.snd, x.val.fst)), {
      apply myset.setext,
      intro z,
      split; assume hz, {
        existsi (⟨(z.snd, z.fst), hz⟩: subtype {xy : β × α | xy.fst = y}),
        cases z,
        refl,
      }, {
        cases hz with z' hz',
        rw ←hz',
        from z'.property,
      },
    },
    rw this, clear this,
    assumption,
  }, {
    rw ←myset.exists_iff_neq_empty,
    existsi (x, y),
    split, {
      from rfl,
    }, {
      from rfl,
    },
  },
end

theorem product_connected
(X: topological_space α) (Y: topological_space β)
(hXcn: is_connected X) (hYcn: is_connected Y):
is_connected (product_topology X Y) :=
begin
  apply surjective_image_connected _ _ _ (univ_homeomorphism _).g_continuous, {
    intro a,
    existsi (⟨a, trivial⟩: subtype myset.univ),
    refl,
  }, {
    by_cases hXe: (myset.univ: myset (α × β)) = ∅, {
      rw hXe,
      apply empty_connected,
    }, {
      cases myset.exists_iff_neq_empty.mpr hXe with xy hxy,
      suffices h: ⋃₀ myset.imageu (λ y: β, (λ xy': α × β, xy'.fst = xy.fst ∨ xy'.snd = y)) = myset.univ, {
        rw ←h,
        apply s_union_of_overlapping_connected, {
          intro U,
          assume hUc,
          cases hUc with y hy,
          rw ←hy,
          apply cross_connected; assumption,
        }, {
          intros U V,
          assume hUc hVc,
          rw ←myset.exists_iff_neq_empty,
          existsi xy,
          split, {
            cases hUc with _ hUc,
            rw ←hUc,
            left,
            refl,
          }, {
            cases hVc with _ hVc,
            rw ←hVc,
            left,
            refl,
          },
        },
      }, {
        apply myset.setext,
        intro xy'',
        split; assume hx, {
          trivial,
        }, {
          existsi λ (xy' : α × β), xy'.fst = xy.fst ∨ xy'.snd = xy''.snd,
          split, {
            existsi xy''.snd,
            refl,
          }, {
            right,
            refl,
          },
        },
      },
    },
  },
end

end topological_space

end hidden
