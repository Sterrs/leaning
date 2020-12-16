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
    apply funext,
    intro x,
    apply propext,
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

theorem image_connected
(X: topological_space α) (Y: topological_space β)
(f: α → β) (hfc: is_continuous X Y f):
is_connected X → is_connected (subspace_topology Y (myset.image f myset.univ)) :=
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
  have hpreUo := @continuous_to_image _ _ X Y f hfc U hUo,
  have hpreVo := @continuous_to_image _ _ X Y f hfc V hVo,
  apply hXc,
  existsi (myset.inverse_image (myset.function_restrict_to_image f) U),
  existsi (myset.inverse_image (myset.function_restrict_to_image f) V),
  split, {
    assume hpreUe,
    have := myset.nonempty_inverse_image_surjective f U hUne,
    contradiction,
  }, split, {
    assume hpreVe,
    have := myset.nonempty_inverse_image_surjective f V hVne,
    contradiction,
  }, split, {
    have := @continuous_to_image _ _ X Y f hfc U hUo,
    assumption,
  }, split, {
    have := @continuous_to_image _ _ X Y f hfc V hVo,
    assumption,
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

theorem empty_connected
(X: topological_space α):
is_connected (subspace_topology X ∅) :=
begin
  assume hXdc,
  cases hXdc with U hXdc,
  cases hXdc with V hXdc,
  apply hXdc.left,
  apply funext,
  intro x,
  apply propext,
  split; assume h, {
    from x.property,
  }, {
    exfalso, from h,
  },
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
    apply funext,
    intro z,
    apply propext,
    split; assume h, {
      cases h, contradiction,
    }, {
      exfalso, from h,
    },
  }, {
    apply funext,
    intro z,
    apply propext,
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
      apply funext,
      intro z,
      apply propext,
      split, {
        assume h,
        cases h,
        contradiction,
      }, {
        assume h,
        exfalso, from h,
      },
    }, {
      apply funext,
      intro z,
      apply propext,
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
  rw hxy,
  rw hyz,
  rw hzw,
end

-- does this even end up being faster (:
theorem union_of_overlapping_connected
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
      },    },
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

end topological_space

end hidden
