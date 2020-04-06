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

@[simp]
theorem coe_succ: (↑(succ a): myint) = ↑a + 1 := rfl

@[simp] theorem nat_nat_add: (↑a: myint) + ↑b = ↑(a + b) := rfl

@[simp]
theorem neg_nat_add: -[1+ a] + ↑b = sub_nat_nat b (succ a) := rfl

@[simp]
theorem nat_neg_add: ↑a + -[1+ b] = sub_nat_nat a (succ b) := rfl

@[simp]
theorem neg_neg_add: -[1+ a] + -[1+ b] = -[1+ succ (a + b)] := rfl


theorem of_nat_succ_add_one: of_nat (succ a) = of_nat a + 1 := rfl

@[simp]
theorem add_comm: ∀ {m n : myint}, m + n = n + m
| (of_nat a) (of_nat b) := by rw [←coe_nat_eq, ←coe_nat_eq,
nat_nat_add, nat_nat_add, of_nat_cancel, hidden.add_comm]
| (of_nat a) -[1+ b]    := by rw [←coe_nat_eq, nat_neg_add,
neg_nat_add]
| -[1+ a]    (of_nat b) := by rw [←coe_nat_eq, neg_nat_add, nat_neg_add]
| -[1+ a]    -[1+ b] := by rw [neg_neg_add, neg_neg_add, hidden.add_comm]

@[simp]
theorem zero_add: ∀ m : myint, 0 + m = m
| (of_nat m) := by rw [←zero_nat, ←coe_nat_eq, nat_nat_add, hidden.zero_add]
| -[1+ n] := by rw [←zero_nat, nat_neg_add]; refl

@[simp]
theorem add_zero: m + 0 = m :=
begin
  have := @zero_add m,
  rwa add_comm,
end

-- Stupid but useful
private theorem one: (1:mynat) = succ 0 := rfl

@[simp]
theorem succ_of_sub_succ: ∀ {a b : mynat},
sub_nat_nat a (succ b) + 1 = sub_nat_nat a b
| zero zero := rfl
| zero (succ b) :=
by rw [zz, zero_sub_neg, zero_sub_neg, neg_succ, neg_succ,
  ←one_nat, neg_nat_add, one, sub_succ_succ, zero_sub_neg,
  neg_succ]
| (succ a) zero :=
by rw [zz, sub_succ_succ, nat_sub_zero, nat_sub_zero, ←one_nat,
  nat_nat_add, add_one_succ]
| (succ a) (succ b) :=
-- This line is particularly interesting, by using
-- succ_of_sub_succ we using recursion
by rw [sub_succ_succ, sub_succ_succ, succ_of_sub_succ]

@[simp]
theorem sub_nat_succ:
∀ {b : mynat}, sub_nat_nat (succ a) b = sub_nat_nat a b + 1
| zero     := by rw [←succ_of_sub_succ, sub_succ_succ]
| (succ b) := by rw [succ_of_sub_succ, sub_succ_succ]

-- TODO: $@!*?%#
private lemma add_one_switch: ∀ {m n : myint},
(m + n) + 1 = (m + 1) + n
| (of_nat a) (of_nat b) :=
begin
  rw ←one_nat,
  repeat {rw [←coe_nat_eq]},
  repeat {rw [nat_nat_add]},
  rw [of_nat_cancel, hidden.add_assoc,
      hidden.add_comm b, ←hidden.add_assoc],
end
| (of_nat a) -[1+ b] :=
begin
  rw ←one_nat,
  repeat {rw ←coe_nat_eq},
  rw [nat_neg_add, nat_nat_add, nat_neg_add, one_nat,
      ←sub_nat_succ, add_one_succ],
end
| -[1+ a] (of_nat b) :=
begin
  rw ←one_nat,
  repeat {rw ←coe_nat_eq},
  rw [neg_nat_add, neg_nat_add, one_nat, one, sub_succ_succ,
      ←sub_nat_succ, zero_sub_neg, sub_succ_succ],
  cases a,
    rw [zz, nat_sub_zero, neg_of_nat_zero, zero_add],
  rw [neg_succ, neg_nat_add],
end
| -[1+ a] -[1+ b] :=
begin
  rw [←one_nat, neg_nat_add, neg_neg_add, neg_nat_add, one,
  sub_succ_succ, sub_succ_succ, zero_sub_neg, zero_sub_neg, neg_succ],
  cases a,
    rw [zz, neg_of_nat_zero, zero_add, hidden.zero_add],
  rw [succ_add, neg_succ, neg_neg_add],
end

theorem sub_nat_add: ∀ {a},
sub_nat_nat (a + b) c = ↑a + sub_nat_nat b c
| zero     := by
  rw [zz, hidden.zero_add, zero_nat, zero_add]
| (succ a) := by rw [succ_add, sub_nat_succ, sub_nat_add,
add_one_switch, ←one_nat, nat_nat_add, add_one_succ]

theorem sub_neg_add: ∀ {c},
sub_nat_nat a (b + succ c) = -[1+ c] + sub_nat_nat a b
| zero     :=
begin
  rw [zz, add_succ, hidden.add_zero],
  sorry,
end
| (succ c) :=
begin
  sorry,
end

-- 8 cases...
theorem add_assoc : ∀ {m n k : myint}, m + n + k = m + (n + k)
| (of_nat a) (of_nat b) (of_nat c) :=
by repeat {rw ←coe_nat_eq <|> rw nat_nat_add}; rw hidden.add_assoc
| (of_nat a) (of_nat b) -[1+ c]    :=
by  rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_add, nat_neg_add,
      nat_neg_add, sub_nat_add]
| (of_nat a) -[1+ b]    (of_nat c) :=
by rw [←coe_nat_eq, ←coe_nat_eq, neg_nat_add, nat_neg_add,
      add_comm, ←sub_nat_add, ←sub_nat_add, hidden.add_comm]
| (of_nat a) -[1+ b]    -[1+ c]    :=
by rw [←coe_nat_eq, neg_neg_add, nat_neg_add, nat_neg_add,
  add_comm, ←sub_neg_add, succ_add, add_succ]
| -[1+ a]    (of_nat b) (of_nat c) :=
by rw [←coe_nat_eq, ←coe_nat_eq, neg_nat_add, nat_nat_add,
      neg_nat_add, add_comm, ←sub_nat_add, hidden.add_comm]
| -[1+ a]    (of_nat b) -[1+ c]    :=
by rw [←coe_nat_eq, neg_nat_add, nat_neg_add, ←sub_neg_add,
  add_comm, ←sub_neg_add, succ_add, add_succ, succ_add,
  add_succ, hidden.add_comm]
| -[1+ a]    -[1+ b]    (of_nat c) :=
begin
  rw [←coe_nat_eq, neg_neg_add, neg_nat_add, neg_nat_add,
  ←sub_neg_add, succ_add, add_succ, hidden.add_comm],
end
| -[1+ a]    -[1+ b]    -[1+ c]    :=
by repeat {rw neg_neg_add};
  rw [neg_succ_of_nat_cancel, succ_add, add_succ, hidden.add_assoc]

private lemma add_cancel_mp: ∀ k : myint, m + k = n + k → m = n
| (of_nat a) :=
begin
  assume h,
  induction a with a ha,
    rwa [zz, of_nat_zero, add_zero, add_zero] at h,
  {
    rw [of_nat_succ_add_one] at h,
    sorry,
  },
end
| -[1+ a] :=
begin
  assume h,
  induction a with a ha,
  sorry,
  sorry,
end

theorem add_cancel (k : myint) : m + k = n + k ↔ m = n :=
begin
  sorry,
end

theorem add_self_neg: ∀ m : myint, m + (-m) = 0
| (of_nat a) := match a with
| zero := by rw [zz, of_nat_zero, zero_add, neg_zero]
| (succ a) :=
begin
  rw [←coe_nat_eq, coe_succ],
  sorry,
end
end
| -[1+ a] := sorry

theorem add_neg_self : -m + m = 0 := by
rw add_comm; apply add_self_neg

end myint
end hidden
