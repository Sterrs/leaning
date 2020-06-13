import .le
import .mul

namespace hidden

namespace myrat

def lt (x y : myrat) := ¬y ≤ x

instance: has_lt myrat := ⟨lt⟩

theorem zero_lt_mul (a b: myrat): 0 < a → 0 < b → 0 < a * b :=
begin
    assume hapos hbpos,
    sorry,
end

theorem lt_add_left {a b : myrat} (c : myrat) : a < b ↔ c + a < c + b :=
sorry

theorem lt_add_right {a b : myrat} (c : myrat) : a < b ↔ a + c < b + c :=
sorry

theorem lt_comb (a b c d: myrat): a < b → c < d → a + c < b + d := sorry

theorem lt_le_chain (a b c: myrat): a < b → b ≤ c → a < c := sorry

theorem le_lt_chain (a b c: myrat): a ≤ b → b < c → a < c := sorry

theorem abs_diff_lt_left {a b c : myrat} : abs (a - b) < c → b - c < a := sorry

theorem abs_diff_lt_right {a b c : myrat} : abs (a - b) < c → a < b + c := sorry

@[trans]
theorem lt_trans {a b c : myrat} : a < b → b < c → a < c := sorry

theorem half_pos {ε : myrat} : 0 < ε → 0 < ε / 2 := sorry

theorem exists_between (a c : myrat) :
∃ b : myrat, a < b ∧ b < c :=
begin
  existsi (a + c) / 2,
  sorry,
end

end myrat

end hidden
