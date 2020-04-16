import .le

namespace hidden

namespace myrat

def lt (x y : myrat) := ¬y ≤ x

instance: has_lt myrat := ⟨lt⟩

end myrat

end hidden
