import .myint

namespace hidden

namespace myint

def le (m n : myint) := ∃ k : mynat, n = m + ↑k

instance: has_le myint := ⟨le⟩

end myint

end hidden
