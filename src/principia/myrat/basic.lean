import .frac

namespace hidden

open frac

def myrat := quotient frac.setoid

namespace myrat

def add : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x + y⟧) add_well_defined

instance: has_add myrat := ⟨add⟩

def mul : myrat → myrat → myrat :=
quotient.lift₂ (λ x y, ⟦x * y⟧) mul_well_defined

instance: has_mul myrat := ⟨mul⟩

def inv : myrat → myrat :=
quotient.lift (λ x, ⟦x⁻¹⟧) inv_well_defined

instance: has_inv myrat := ⟨inv⟩

end myrat

end hidden
