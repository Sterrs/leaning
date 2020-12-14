import .mynat.lt

namespace hidden

def sequence (α : Type) := mynat → α

namespace sequence

variable {α : Type}

def is_increasing (k_n: mynat → mynat): Prop :=
∀ m n: mynat, m < n → k_n m < k_n n

def subsequence
(a: sequence α) (k_n: mynat → mynat)
(h_incr: is_increasing k_n): sequence α :=
a ∘ k_n

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

-- sum from k = 0 to n - 1 of term(k)
-- a bit unconventional, but this is the best way I could think of
-- to not have to have weird special cases with 0
def sum {α : Type} [has_add α] [has_zero α]
(seq: sequence α): sequence α
| 0        := 0
| (mynat.succ n) := sum n + seq n

def product {β : Type} [has_mul β] [has_one β]
(term : sequence β) : sequence β
| 0        := 1
| (mynat.succ n) := product n * term n

end sequence

end hidden
