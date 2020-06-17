import ..mynat.dvd
import .le

namespace hidden
namespace quotint

def dvd (m n : quotint) := ∃ k : quotint, n = k * m

instance: has_dvd quotint := ⟨dvd⟩

def coprime (m n : quotint) := ∀ k: quotint, k ∣ m → k ∣ n → (k = 1 ∨ k = -1)

variables {m n : quotint}

-- Perhaps this will allow all the mynat dvd theorems to generalise
theorem int_dvd_iff_abs_dvd :
m ∣ n ↔ (abs m) ∣ (abs n) :=
begin
  split; assume h, {
    cases h with k hk,
    existsi (abs k),
    sorry,
  }, {
    cases h with k hk,
    sorry,
  },
end

end quotint
end hidden
