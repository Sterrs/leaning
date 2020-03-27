import .finite

-- Definitions and theorems relating to countability
namespace hidden

universes u v w

open myset

variables {α : Type u} {β : Type v} {γ : Type w}

def countable {α : Type u} (s : myset α) : Prop :=
finite s ∨ equinumerous (all_of mynat) s
def uncountable {α : Type u} (s : myset α) : Prop :=
¬countable s

-- Proven, given some theorems in finite.lean
theorem uncountability_of_power_set_of_naturals:
uncountable (power_set (all_of mynat)) :=
begin
  assume h,
  cases h with hfinite hcountinf, {
    -- Using revert here is quite nice
    revert hfinite,
    -- Although this line is stupid
    suffices : infinite (power_set (all_of mynat)), from this,
    rw ←inf_iff_powerset_inf (all_of mynat),
    from naturals_infinite,
  }, {
    have := card_ne_power_set (all_of mynat),
    contradiction,
  },
end

end hidden
