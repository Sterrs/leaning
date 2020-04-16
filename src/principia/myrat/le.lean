import .add

namespace hidden

namespace frac

def le (x y : frac): Prop :=
x.num * y.denom ≤ y.num * x.denom

instance: has_le frac := ⟨le⟩

theorem le_well_defined (a x b y : frac) :
a ≈ b → x ≈ y → (a ≤ x) = (b ≤ y) :=
begin
  assume hab hxy,
  apply propext,
  split; assume h, {
    sorry,
  }, {
    sorry,
  },
end

end frac

namespace myrat

def le := quotient.lift₂ (λ x y, x ≤ y) frac.le_well_defined

instance: has_le myrat := ⟨le⟩

end myrat

end hidden
