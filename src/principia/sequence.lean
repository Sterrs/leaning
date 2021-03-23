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

theorem subsequence_growth
(k_n: mynat → mynat) (h_incr: is_increasing k_n) (n: mynat):
n ≤ k_n n :=
begin
  induction n with n ih_n, {
    from mynat.zero_le,
  }, {
    transitivity (k_n n).succ, {
      apply mynat.le_add (1: mynat),
      assumption,
    }, {
      rw ←mynat.lt_iff_succ_le,
      apply h_incr,
      apply @mynat.lt_to_add_succ n (0: mynat),
    },
  },
end

theorem subsequence_nonstrict
(k_n: mynat → mynat) (h_incr: is_increasing k_n)
(m n: mynat) (hmn: m ≤ n):
k_n m ≤ k_n n :=
begin
  rw mynat.le_iff_lt_or_eq at hmn,
  cases hmn with hmn hmn, {
    apply mynat.lt_impl_le,
    apply h_incr,
    assumption,
  }, {
    rw hmn,
  },
end

theorem subsequence_eventual_growth
(k_n: mynat → mynat) (h_incr: is_increasing k_n)
(m n: mynat) (hmn: m ≤ n):
m ≤ k_n n :=
begin
  transitivity k_n m, {
    apply subsequence_growth _ h_incr,
  }, {
    apply subsequence_nonstrict; assumption,
  },
end

theorem locally_increasing_impl_increasing
(k_n: mynat → mynat)
(h_incr: ∀ n: mynat, k_n n < (k_n n.succ)):
is_increasing k_n :=
begin
  intros m n,
  assume hmn,
  rw mynat.lt_iff_succ_le at hmn,
  cases hmn with d hd,
  rw hd, clear hd n,
  induction d with d ih_d, {
    apply h_incr,
  }, {
    transitivity k_n (m.succ + d), {
      assumption,
    }, {
      apply h_incr,
    },
  },
end

-- Coerce a value into a sequence of that value.
-- e.g. ↑0 = 0, 0, 0, 0, ... = λ k, 0
-- This is probably bad so might remove this

instance: has_coe α (sequence α) := ⟨λ a, (λ k, a)⟩

@[simp]
theorem coe_seq (a : α) : (↑a: sequence α) = (λ k: mynat, a) := rfl

@[simp]
theorem coe_triv (a : α) (n: mynat): (↑a: sequence α) n = a := rfl

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

def accumulate
{α : Type} (f: α → α → α) (dflt: α) (seq: sequence α): sequence α
| 0              := dflt
| (mynat.succ n) := f (accumulate n) (seq n)

-- sum from k = 0 to n - 1 of term(k)
-- a bit unconventional, but this is the best way I could think of
-- to not have to have weird special cases with 0
def sum {α : Type} [has_add α] [has_zero α]
(seq: sequence α): sequence α
:= accumulate (+) 0 seq

def product {β : Type} [has_mul β] [has_one β]
(seq: sequence β): sequence β
:= accumulate (*) 1 seq

end sequence

end hidden
