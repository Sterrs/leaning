import .mynat.nat_sub

namespace hidden

def sequence (α : Type) := mynat → α

namespace sequence

variable {α : Type}

-- Coerce a value into a sequence of that value.
-- e.g. ↑0 = 0, 0, 0, 0, ... = λ k, 0
-- This is probably bad so might remove this

instance: has_coe α (sequence α) := ⟨λ a, (λ k, a)⟩

@[simp]
theorem coe_seq (a : α) : (↑a:sequence α) = (λ k : mynat, a) := rfl

@[simp]
theorem coe_triv (a : α) (n :mynat): (↑a:sequence α) n = a := rfl

variables [has_add α] {β : Type} [has_mul β]

def add (a b : sequence α): sequence α := λ k , a k + b k
instance: has_add (sequence α) := ⟨add⟩
-- Yuck...
@[simp] theorem addition (a b : sequence α) (n : mynat) :
(a + b) n = a n + b n := rfl
@[simp] theorem coe_add (a : α) (s : sequence α) (n : mynat):
(↑a + s) n = a + (s n) := rfl
@[simp] theorem add_coe (s : sequence α) (a : α) (n : mynat):
(s + ↑a) n = (s n) + a := rfl

def mul (a b : sequence β): sequence β := λ k, a k * b k
instance: has_mul (sequence β) := ⟨mul⟩
@[simp] theorem multiplication (a b : sequence β) (n : mynat) :
(a * b) n = a n * b n := rfl
@[simp] theorem coe_mul (b : β) (s : sequence β) (n : mynat):
(↑b * s) n = b * (s n) := rfl
@[simp] theorem mul_coe (s : sequence β) (b : β) (n : mynat):
(s * ↑b) n = (s n) * b := rfl

variables [has_zero α] [has_one β]

instance: has_zero (sequence α) := ⟨λ k, 0⟩
instance: has_one (sequence β) := ⟨λ k, 1⟩

end sequence

end hidden
