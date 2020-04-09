import .dvd
import .nat_sub
import .induction

namespace hidden

open mynat

private lemma mod_lemma {m n : mynat} :
 0 < n ∧ n ≤ m → m - n < m :=
begin
  assume h,
  cases h with h0n hnm,
  have : 0 < m,
    apply lt_le_chain n,
      assumption,
    assumption,
  rw zero_lt_iff_succ at h0n,
  cases h0n with k hk,
  rw hk,
  apply sub_succ_lt,
  from nzero_iff_zero_lt.mpr this,
end

-- I copied this from Lean source :(
private def mod.F (m : mynat)
(f : Π k, k < m → mynat → mynat) (n : mynat) : mynat :=
if h : 0 < n ∧ n ≤ m then f (m - n) (mod_lemma h) n else m

def mod := well_founded.fix lt_well_founded mod.F

instance: has_mod mynat := ⟨mod⟩

variables {m n k : mynat}

theorem mod_zero: ∀ {m : mynat}, m % 0 = m
| zero     := rfl
| (succ m) := rfl

theorem zero_mod: ∀ {m : mynat}, 0 % m = 0
| zero     := rfl
| (succ m) := rfl

theorem zero_mod_iff_dvd: m % n = 0 ↔ m ∣ n :=
begin
  sorry, -- Not a clue
end

end hidden
