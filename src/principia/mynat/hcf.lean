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

lemma mod_def_aux (x y : mynat) : x % y = if h : 0 < y ∧ y ≤ x then (x - y) % y else x :=
congr_fun (well_founded.fix_eq lt_well_founded mod.F x) y

variables {m n k : mynat}

theorem mod_zero: ∀ {m : mynat}, m % 0 = m
| zero     := rfl
| (succ m) := rfl

theorem zero_mod: ∀ {m : mynat}, 0 % m = 0
| zero     := rfl
| (succ m) := rfl

theorem mod_cancel: (m + n) % n = m % n :=
begin
  rw mod_def_aux,
  cases n, {
    rw dif_neg _, {
      rw [zz, mod_zero],
      refl,
    }, {
      from (λ ⟨h, _⟩, lt_nrefl h),
    },
  }, {
    rw dif_pos _, {
      rw add_sub,
    }, {
      split, {
        from zero_lt_succ,
      }, {
        rw add_comm,
        from le_to_add,
      }
    }
  }
end

theorem mod_cancel_lots: (m + k * n) % n = m % n :=
begin
  induction k with k' hk', {
    rw [zz, zero_mul, add_zero],
  }, {
    rw [succ_mul, ←add_assoc, mod_cancel, hk'],
  },
end

theorem zero_mod_iff_dvd: m % n = 0 ↔ n ∣ m :=
begin
  split, {
    -- probably we'll need to define div before we can do this
    sorry,
  }, {
    assume hnm,
    cases hnm with k hk,
    rw hk,
    rw ←zero_add (k * n),
    rw mod_cancel_lots,
    rw zero_mod,
  },
end

end hidden
