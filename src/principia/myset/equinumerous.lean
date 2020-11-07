-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..logic
import .functions

namespace hidden

universes u v w

open myset

variables {α : Type u} {β : Type v} {γ : Type w}

section definitions
  variables (s : myset α) (t : myset β)

  def card_le : Prop :=
  ∃ f : α → β, ∃ h: well_defined s t f, (injective h)
  def card_ge : Prop :=
  ∃ f : α → β, ∃ h: well_defined s t f, (surjective h)
  -- of same cardinality
  def equinumerous : Prop :=
  ∃ f : α → β, ∃ h: well_defined s t f, (bijective h)

end definitions

-- The trivial function from a set to itself is well defined
theorem trivial_well_defined (s : myset α):
well_defined s s (λ a, a) :=
begin
  intro a,
  assume h,
  assumption,
end
theorem trivial_injective (s : myset α):
injective (trivial_well_defined s) :=
begin
  intros a₁ a₂,
  assume h₁ h₂ hneq,
  assumption,
end
theorem trivial_surjective (s : myset α):
surjective (trivial_well_defined s) :=
begin
  intro a,
  assume h,
  existsi a,
  split,
    from h,
  refl,
end

@[refl]
theorem card_le_refl (s : myset α) :
card_le s s :=
begin
  let f := (λ a : α, a),
  let h := trivial_well_defined s,
  existsi f,
  existsi h,
  from trivial_injective s,
end
@[refl]
theorem card_ge_refl (s : myset α) :
card_ge s s :=
begin
  let f := (λ a : α, a),
  let h := trivial_well_defined s,
  existsi f,
  existsi h,
  from trivial_surjective s,
end
@[refl]
theorem equinumerous_refl (s : myset α) :
equinumerous s s :=
begin
  let f := (λ a : α, a),
  have h := trivial_well_defined s,
  existsi f,
  existsi h,
  split,
    from trivial_injective s,
  from trivial_surjective s,
end

@[symm]
theorem equinumerous_symm (s : myset α) (t : myset β) :
equinumerous s t → equinumerous t s := sorry

@[trans]
theorem equinumerous_trans (r : myset α) (s : myset β) (t : myset γ) :
equinumerous r s → equinumerous s t → equinumerous r t :=
begin
  assume hrs hst,
  cases hrs with f hf,
  cases hf with hwf hf,
  cases hst with g hg,
  cases hg with hwg hg,
  existsi g ∘ f,
  existsi composition_well_defined hwf hwg,
  from bij_bij hwf hwg hf hg,
end

section -- for classical logic
open classical
local attribute [instance] prop_decidable

theorem card_ne_power_set (s : myset α) :
¬equinumerous s (power_set s) :=
begin
  assume heq,
  cases heq with f hf,
  cases hf with hwell hbi,
  cases hbi with hinj hsurj,
  suffices hcontra : ∃ t : myset α, t ∈ (power_set s) ∧
                     ∀ a : α, a ∈ s → f a ≠ t, {
    cases hcontra with t ht,
    cases hsurj t ht.left with preim hpreim,
    from ht.right preim hpreim.left hpreim.right,
  },
  let t := λ a : α, a ∈ s ∧ ¬(a ∈ f a),
  existsi t,
  split, {
    intro a,
    assume hta,
    from hta.left,
  }, {
    intro a,
    assume h heq,
    have hnta : ¬(t a), {
      assume hta,
      have haninfa := hta.right,
      rw heq at haninfa,
      contradiction,
    },
    have hta : t a, {
      rw not_and at hnta,
      have hnin := hnta h,
      rw [not_not, heq] at hnin,
      from hnin,
    },
    contradiction,
  },
end
end -- for classical logic

theorem schroeder_bernstein_theorem
{s : myset α} {t : myset β}:
card_le s t → card_ge s t → equinumerous s t := sorry

variables {r : myset α} {s : myset β} {t : myset γ}
variables {f : α → β} (hwf : well_defined r s f)

include hwf

def restriction (r': myset α):
r' ⊆ r → (α → β) := (λ _ a, f a)

omit hwf

theorem restriction_well_defined
(r': myset α) (hrss: r' ⊆ r):
well_defined r' s (restriction hwf r' hrss) :=
begin
  intro a,
  assume har',
  apply hwf,
  apply hrss,
  from har',
end

-- this can probably be shorter but I keep getting confused by all the
-- definitions
theorem restriction_injective
(r': myset α) (hrss: r' ⊆ r)
(hif: injective hwf):
injective (restriction_well_defined hwf r' hrss) :=
begin
  intros a b,
  assume har' hbr' hrarb,
  apply hif _ _ _ _ _, {
    from hrss _ har',
  }, {
    from hrss _ hbr',
  }, {
    from hrarb,
  },
end

end hidden
