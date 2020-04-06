import .basic
import .add

namespace hidden

namespace myint

-- Old defn
-- def le (m n : myint) := ∃ k : mynat, n = m + ↑k

-- I'm going with this because it should allow us to use more mynat ≤
-- theorems
def le: myint → myint → Prop
| (of_nat a) (of_nat b) := a ≤ b
| (of_nat a) -[1+ b] := false
| -[1+ a] (of_nat b) := true
| -[1+ a] -[1+ b] := b ≤ a

instance: has_le myint := ⟨le⟩

variables {m n k : myint}
variables {a b c : mynat}

@[simp]
theorem nat_nat_le: (↑a:myint) ≤ ↑b ↔ a ≤ b := by trivial

@[simp]
theorem nat_neg_le: ¬(↑a ≤ -[1+ b]) :=
by { rw coe_nat_eq, assume h, from h }

@[simp]
theorem neg_nat_le: -[1+ a] ≤ ↑b := by trivial

@[simp]
theorem neg_neg_le: -[1+ a] ≤ -[1+ b] ↔ b ≤ a := by trivial

private lemma le_to_add_nat: ∀ {m:myint}, m ≤ m + ↑a
| (of_nat b) := sorry
| -[1+ b] := sorry

private theorem le_iff_exists_nat_mpr: ∀ {m n : myint},
m ≤ n → ∃ c : mynat, n = m + ↑c
| (of_nat a) (of_nat b) := assume h,
begin

end
| (of_nat a) -[1+ b] := sorry
| -[1+ a] (of_nat b) := sorry
| -[1+ a] -[1+ b] := sorry

-- Show old defn of ≤ is equivalent (should also be useful to prove)
theorem le_iff_exists_nat: m ≤ n ↔ ∃ a : mynat, n = m + ↑a :=
begin
  split; assume h, {
    sorry,
  }, {
    cases h with a ha,
    rw ha,
    apply le_to_add_nat,
  },
end

end myint

end hidden
