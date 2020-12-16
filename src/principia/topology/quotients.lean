import .topological_space

namespace hidden

namespace topological_space

variables {α β γ: Type}

open classical

local attribute [instance] classical.prop_decidable

def quotient_topology
(X: topological_space α) (R: setoid α):
topological_space (quotient R) := {
  is_open := {V | X.is_open {x: α | ⟦x⟧ ∈ V}},
  univ_open :=
  begin
    from X.univ_open,
  end,
  empty_open :=
  begin
    from X.empty_open,
  end,
  open_union_open :=
  begin
    intro S,
    assume hSo,
    apply (open_iff_neighbourhood_forall _ _).mpr,
    intro x,
    assume hxUS,
    cases hxUS with U hU,
    cases hU with hU hxU,
    existsi {y : α | ⟦y⟧ ∈ U},
    split, {
      apply hSo,
      from hU,
    }, split, {
      from hxU,
    }, {
      intro y,
      assume hyU,
      existsi U,
      split, {
        from hU,
      }, {
        from hyU,
      },
    },
  end,
  open_intersection_open :=
  begin
    intros U V,
    assume hUo hVo,
    have: {x : α | ⟦x⟧ ∈ U ∩ V} = {x | ⟦x⟧ ∈ U} ∩ {x | ⟦x⟧ ∈ V}, {
      from myset.inverse_image_intersection (λ x, ⟦x⟧) _ _,
    },
    change X.is_open {x : α | ⟦x⟧ ∈ U ∩ V},
    rw this,
    apply X.open_intersection_open, {
      from hUo,
    }, {
      from hVo,
    },
  end,
}

end topological_space

end hidden