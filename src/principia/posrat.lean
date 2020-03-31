import .le

namespace hidden
open mynat

structure posrat_pair :=
(a : mynat)
(b : mynat)
(hbne0 : b ≠ 0)

def posrat_eq (q₁ q₂ : posrat_pair) : Prop :=
q₁.a * q₂.b = q₁.b * q₂.a

namespace rat_eq
  theorem refl :
  ∀ q : posrat_pair, posrat_eq q q :=
  begin
    intro q,
    unfold posrat_eq,
    rw mul_comm,
  end

  theorem symm :
  ∀ q₁ q₂ : posrat_pair, posrat_eq q₁ q₂ → posrat_eq q₂ q₁ :=
  begin
    intros q₁ q₂,
    assume h,
    unfold posrat_eq at h,
    unfold posrat_eq,
    symmetry,
    conv {
      congr,
      rw mul_comm,
      skip,
      rw mul_comm,
    },
    assumption,
  end

  theorem trans :
  ∀ p q r : posrat_pair,
  posrat_eq p q → posrat_eq q r → posrat_eq p r :=
  begin
    intros p q r,
    assume hpq hqr,
    unfold posrat_eq at hpq hqr,
    unfold posrat_eq,
    sorry,
  end
end rat_eq

-- def posrat := quot rat_eq

end hidden
