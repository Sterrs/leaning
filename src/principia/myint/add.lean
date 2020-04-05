import .basic


namespace hidden
namespace myint

open mynat
open myint

def add: myint → myint → myint
| (of_nat m) (of_nat n) := of_nat (m + n)
| -[1+ m] (of_nat n)    := sub_nat_nat n (succ m)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m] -[1+ n]       := -[1+ succ (m + n)]

instance: has_add myint := ⟨add⟩

-- maybe this is done automatically anyway, idk
def sub (m n: myint): myint := m + (-n)
instance: has_sub myint := ⟨sub⟩

variables {m n k : myint}
variables {a b c : mynat}

@[simp] theorem nat_nat_add: (↑a: myint) + ↑b = ↑(a + b) := rfl

@[simp]
theorem neg_nat_add: -[1+ a] + ↑b = sub_nat_nat b (succ a) := rfl

@[simp]
theorem nat_neg_add: ↑a + -[1+ b] = sub_nat_nat a (succ b) := rfl

@[simp]
theorem neg_neg_add: -[1+ a] + -[1+ b] = -[1+ succ (a + b)] := rfl


theorem of_nat_succ_add_one: of_nat (succ a) = of_nat a + 1 := rfl

@[simp]
theorem add_comm: m + n = n + m :=
begin
  cases m,
  cases n,
  simp,
  simp,
  cases n,
  simp,
  simp,
end

@[simp]
theorem zero_add: 0 + m = m :=
begin
  cases m,
  rw ←zero_nat,
  simp,
  rw ←zero_nat,
  simp,
end

@[simp]
theorem add_zero: m + 0 = m :=
begin
  have := @zero_add m,
  rwa add_comm,
end

@[simp]
theorem succ_of_sub_succ:
sub_nat_nat a (succ b) + 1 = sub_nat_nat a b :=
begin
  cases m',
    simp,
    sorry,
  rw sub_succ_succ,
  sorry,
end

@[simp]
theorem sub_nat_succ:
sub_nat_nat (succ a) b = sub_nat_nat a b + 1 :=
begin
  induction b with b hb,
  simp,
  rw add_comm,
  refl,
  simp,
end

@[simp]
theorem coe_succ: (↑(succ a): myint) = ↑a + 1 := rfl

@[simp]
theorem sub_nat_add:
sub_nat_nat (a + b) c = a + sub_nat_nat b c :=
begin
  induction a with a ha,
  simp,
  rw zero_nat,
  simp,
  rw [succ_add, sub_nat_succ, ha],
  sorry,
end

theorem add_congr (k : myint) : m = n → m + k = n + k := sorry

theorem add_cancel (k : myint) : m + k = n + k → m = n := sorry

theorem add_self_neg : m + (-m) = 0 := sorry

theorem add_neg_self : -m + m = 0 := sorry

theorem add_assoc : m + n + k = m + (n + k) := sorry


end myint
end hidden
