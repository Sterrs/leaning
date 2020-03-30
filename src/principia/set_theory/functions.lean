import logic.basic
import .myset

namespace hidden

universes u v w

open myset

variables {α : Type u} {β : Type v} {γ : Type w}

section definitions
-- A function between two sets is well-defined so long as each element of the
-- first gets sent to an element of the latter
def well_defined (r : myset α) (s : myset β) (f : α → β) : Prop :=
∀ a : α, a ∈ r → f a ∈ s

variables {r : myset α} {s : myset β} {f : α → β}
variable (h : well_defined r s f)

include h

-- These only need to be fed a proof of well-definedness now, which is cleaner
def injective: Prop :=
∀ a₁ a₂ : α, a₁ ∈ r → a₂ ∈ r → f a₁ = f a₂ → a₁ = a₂
def surjective: Prop :=
∀ b : β, b ∈ s → ∃ a : α, a ∈ r ∧ f a = b

def bijective: Prop := injective h ∧ surjective h

omit h

end definitions

section theorems

-- All the following theorems need to be fed proofs of well-definedness, so they
-- are all capable of guessing which types, sets and functions you are talking
-- about. Hence all these arguments are implicit
variables {r : myset α} {s : myset β} {t : myset γ}
variables {f : α → β} {g : β → γ}

section -- This is a section for classical logic
open classical
local attribute [instance] prop_decidable

-- Cannot have a well-defined function from an empty set to a non-empty set
theorem no_wdefined_func_nemp_to_emp
(hnemp : ¬empty r) (hemp : empty s) :
¬well_defined r s f :=
begin
  assume h,
  unfold myset.empty at hnemp, -- necessary for some reason
  -- CLASSICAL USED HERE
  rw not_forall at hnemp,
  cases hnemp with x hx,
  simp at hx,
  have hfxin := h x hx,
  have hfxnin := hemp (f x),
  contradiction,
end
end -- section for classical logic

theorem composition_well_defined:
well_defined r s f → well_defined s t g → well_defined r t (g ∘ f) :=
begin
  assume hwf hwg,
  intro a,
  assume har,
  apply hwg,
  apply hwf,
  assumption,
end

theorem inj_inj (hwf: well_defined r s f) (hwg: well_defined s t g):
injective hwf → injective hwg
  → injective (composition_well_defined hwf hwg) :=
begin
  assume hif hig,
  intros a b,
  assume har hbr hgfagfb,
  apply hif _ _ har hbr,
  apply hig _ _ (hwf a har) (hwf b hbr),
  assumption,
end

-- not the prettiest
theorem surj_surj (hwf: well_defined r s f) (hwg: well_defined s t g):
surjective hwf → surjective hwg
  → surjective (composition_well_defined hwf hwg) :=
begin
  assume hsf hsg,
  intro a,
  assume hat,
  cases hsg a hat with a_g ha_g,
  cases hsf a_g ha_g.left with a_f ha_f,
  existsi a_f,
  split, {
    from ha_f.left,
  }, {
    rw [←ha_g.right, ←ha_f.right],
  },
end

theorem bij_bij (hwf: well_defined r s f) (hwg: well_defined s t g):
bijective hwf → bijective hwg
  → bijective (composition_well_defined hwf hwg) :=
begin
  assume hbf hbg,
  cases hbf with hif hsf,
  cases hbg with hig hsg,
  split, {
    from inj_inj _ _ hif hig,
  }, {
    from surj_surj _ _ hsf hsg,
  }
end

end theorems

end hidden
