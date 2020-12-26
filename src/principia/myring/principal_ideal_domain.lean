import .integral_domain
import .ideal

namespace hidden

namespace myring

variables {α : Type} [myring α] (I J : myset α)

def principal_ideal (r : α) : myset α := { b | ∃ a, r * a = b }

theorem principal_ideal_ideal : ∀ r : α, is_ideal (principal_ideal r) :=
begin
  intro r,
  split, {
    existsi (0: α),
    rw mul_zero,
  }, {
    intros a b ha hb,
    cases ha with s hs,
    cases hb with t ht,
    rw [←ht, ←hs, ←mul_add],
    existsi (s + t),
    refl,
  }, {
    intros s a ha,
    cases ha with t ht,
    existsi t * s,
    rw [←ht, mul_comm s, mul_assoc],
  },
end

structure is_principal_ideal {α : Type} [myring α] (I : myset α) extends is_ideal I : Prop :=
intro :: (is_principal : ∃ r, I = principal_ideal r)

class principal_ideal_domain (α : Type) extends integral_domain α :=
(all_ideals_principal : ∀ I : myset α, is_ideal I → is_principal_ideal I)

end myring

end hidden
