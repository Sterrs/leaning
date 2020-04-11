import ..mynat.dvd
import .le

namespace hidden
namespace myint

def dvd (m n : myint) := ∃ k : myint, n = k * m

instance: has_dvd myint := ⟨dvd⟩

def coprime (m n : myint) := ∀ k: myint, k ∣ m → k ∣ n → (k = 1 ∨ k = -1)

variables {m n : myint}

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

end myint
end hidden
