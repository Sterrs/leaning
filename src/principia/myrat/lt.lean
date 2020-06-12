import .le
import .mul

namespace hidden

namespace myrat

def lt (x y : myrat) := ¬y ≤ x

instance: has_lt myrat := ⟨lt⟩

theorem lt_pos_mul (a b: myrat): 0 < a → 0 < b → 0 < a * b :=
begin
    assume hapos hbpos,
    sorry,
end

theorem triangle_ineq (a b: myrat): abs (a + b) ≤ abs a + abs b :=
begin
    sorry,
end

theorem lt_comb (a b c d: myrat): a < b → c < d → a + c < b + d := sorry

theorem lt_le_chain (a b c: myrat): a < b → b ≤ c → a < c := sorry

theorem le_lt_chain (a b c: myrat): a ≤ b → b < c → a < c := sorry

end myrat

end hidden
