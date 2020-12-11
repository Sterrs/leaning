import .topological_space
import .continuous

namespace hidden

namespace topological_space

variables {α β : Type}

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

end topological_space

end hidden
