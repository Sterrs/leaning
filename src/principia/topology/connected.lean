import .topological_space
import .continuous

namespace hidden

namespace topological_space

variables {α β : Type}

open classical

local attribute [instance] classical.prop_decidable

def is_disconnected (X : topological_space α) : Prop :=
∃ U V : myset α, U ≠ ∅ ∧ V ≠ ∅ ∧ is_open X U ∧ is_open X V ∧ U ∩ V = ∅ ∧ U ∪ V = myset.univ

def is_connected (X : topological_space α) : Prop :=
¬is_disconnected X

theorem image_connected
(X: topological_space α) (Y: topological_space β)
(f: α → β) (hfc: @is_continuous _ _ f X Y):
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

theorem connected_iff_N_image_const
(X: topological_space α):
is_connected X ↔
∀ f: α → mynat,
  @is_continuous _ _ f X (discrete_topology mynat) →
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
    -- show that if U and V disconnect X then indicator function of U
    -- is non-constant
    sorry,
  }
end

theorem union_of_overlapping_connected
(X: topological_space α)
(S: myset (myset α))
(hconn: ∀ U: myset α, U ∈ S →
 is_connected (subspace_topology X U))
(hlap: ∀ U V: myset α,
 U ∈ S → V ∈ S → U ∩ V ≠ ∅):
is_connected (subspace_topology X (⋃₀ S)) :=
begin
  assume hdc,
  cases hdc with W1 hdc,
  cases hdc with W2 hdc,
  sorry,
end

end topological_space

end hidden
