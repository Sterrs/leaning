import .topological_space
import .continuity

namespace hidden

namespace topological_space

variables {α β γ: Type}

open classical

local attribute [instance] classical.prop_decidable

def quotient_topology
(X: topological_space α) (R: setoid α):
topological_space (quotient R) := {
  is_open := {V | X.is_open (myset.inverse_image quotient.mk V)},
  -- equivalently:
  -- is_open := {V | X.is_open {x: α | ⟦x⟧ ∈ V}},
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
    change X.is_open (myset.inverse_image quotient.mk (⋃₀ S)),
    rw myset.inverse_image_sUnion,
    apply X.open_union_open,
    intro U,
    assume hU,
    cases hU with V hV,
    rw ←hV.right,
    apply hSo,
    from hV.left,
  end,
  open_intersection_open :=
  begin
    intros U V,
    assume hUo hVo,
    apply X.open_intersection_open; assumption,
  end,
}

theorem quotient_map_continuous
(X: topological_space α) (R: setoid α):
is_continuous X (quotient_topology X R) quotient.mk :=
λ U, iff.rfl.mp

end topological_space

end hidden