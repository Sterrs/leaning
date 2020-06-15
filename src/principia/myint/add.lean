import .basic

namespace hidden
namespace myint

open mynat
open myint

def add: myint → myint → myint
| (of_nat m) (of_nat n) := of_nat (m + n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    -[1+ n]    := -[1+ succ (m + n)]

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

theorem sub_add_neg: m - n = m + (-n) := rfl

theorem add_comm: ∀ {m n : myint}, m + n = n + m
| (of_nat a) (of_nat b) :=
by rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_add,
       nat_nat_add, of_nat_cancel, mynat.add_comm]
| (of_nat a) -[1+ b]    :=
by rw [←coe_nat_eq, nat_neg_add, neg_nat_add]
| -[1+ a]    (of_nat b) :=
by rw [←coe_nat_eq, neg_nat_add, nat_neg_add]
| -[1+ a]    -[1+ b]    :=
by rw [neg_neg_add, neg_neg_add, mynat.add_comm]

instance add_is_comm: is_commutative myint add :=
⟨assume a b, add_comm⟩

@[simp]
theorem zero_add: ∀ m : myint, 0 + m = m
| (of_nat m) := by rw [←zero_nat, ←coe_nat_eq,
                       nat_nat_add, mynat.zero_add]
| -[1+ n]    := by rw [←zero_nat, nat_neg_add]; refl

@[simp]
theorem add_zero: m + 0 = m :=
begin
  have := @zero_add m,
  rwa add_comm,
end

private theorem negative_one: -(1 : myint) = -↑(1 : mynat) := rfl

theorem neg_distr_coe_one: -(↑a + (1 : myint)) = -(↑a) + -1 :=
begin
  rw [←one_nat, nat_nat_add, add_one_succ,
  neg_coe_succ],
  cases a,
    rw [zz, ←neg_one, ←negative_one, zero_nat, neg_zero, zero_add],
  rw [neg_coe_succ, ←negative_one, neg_one, neg_neg_add,
  mynat.add_zero],
end

-- Stupid but useful
private theorem one: 1 = succ 0 := one_eq_succ_zero.symm

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

theorem sub_nat_succ:
∀ {b : mynat}, sub_nat_nat (succ a) b = sub_nat_nat a b + 1
| zero     := by rw [←succ_of_sub_succ, sub_succ_succ]
| (succ b) := by rw [succ_of_sub_succ, sub_succ_succ]

private lemma add_one_switch: ∀ {m n : myint},
(m + n) + 1 = (m + 1) + n
| (of_nat a) (of_nat b) :=
begin
  rw ←one_nat,
  repeat {rw [←coe_nat_eq]},
  repeat {rw [nat_nat_add]},
  rw [of_nat_cancel, mynat.add_assoc,
      mynat.add_comm b, mynat.add_assoc],
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
    rw [zz, neg_of_nat_zero, zero_add, mynat.zero_add],
  rw [succ_add, neg_succ, neg_neg_add],
end

theorem sub_nat_add: ∀ {a},
sub_nat_nat (a + b) c = ↑a + sub_nat_nat b c
| zero     := by
  rw [zz, mynat.zero_add, zero_nat, zero_add]
| (succ a) := by rw [succ_add, sub_nat_succ, sub_nat_add,
add_one_switch, ←one_nat, nat_nat_add, add_one_succ]

private lemma sub_add_neg_one: ∀ {a b : mynat},
sub_nat_nat a b + -1 = sub_nat_nat a (succ b)
| zero zero :=
by rw [zz, nat_sub_zero, zero_sub_neg, zero_nat, zero_add,
  neg_one, neg_succ]
| zero (succ b) :=
by rw [zz, zero_sub_neg, zero_sub_neg, neg_succ, neg_succ,
  neg_one, neg_neg_add, mynat.add_zero]
| (succ a) zero :=
by rw [zz, sub_succ_succ, nat_sub_zero, nat_sub_zero, neg_one,
  nat_neg_add, sub_succ_succ, nat_sub_zero]
| (succ a) (succ b) :=
by rw [sub_succ_succ, sub_succ_succ, sub_add_neg_one]

private lemma add_neg_one_switch: ∀ {m n : myint},
(m + n) + -1 = (m + -1) + n
| (of_nat a) (of_nat b) :=
by rw [←coe_nat_eq, ←coe_nat_eq, neg_one, nat_nat_add, nat_neg_add,
  nat_neg_add, add_comm, ←sub_nat_add, mynat.add_comm]
| (of_nat a) -[1+ b] :=
begin
  rw [←coe_nat_eq, neg_one, nat_neg_add, nat_neg_add],
  cases a,
    rw [zz, zero_sub_neg, neg_succ, add_comm],
    refl,
  rw [sub_succ_succ, sub_succ_succ, nat_sub_zero, ←neg_one,
  nat_neg_add, sub_add_neg_one],
end
| -[1+ a] (of_nat b) :=
by rw [←coe_nat_eq, neg_one, neg_nat_add, neg_neg_add, ←neg_one,
  neg_nat_add, sub_add_neg_one, mynat.add_zero]
| -[1+ a] -[1+ b] :=
begin
  rw neg_one,
  repeat {rw neg_neg_add},
  rw [mynat.add_zero, mynat.add_zero, succ_add],
end

-- Oh god
private lemma sub_add_neg': ∀ {c : mynat},
sub_nat_nat a b + -↑c = sub_nat_nat a (b + c)
| zero := by rw [zz, zero_nat, neg_zero, add_zero, mynat.add_zero]
| (succ c) :=
by rw [←add_one_succ, ←nat_nat_add, one_nat, neg_distr_coe_one,
  add_comm, ←add_neg_one_switch, @add_comm (-↑c), sub_add_neg',
  sub_add_neg_one, add_one_succ, add_succ]

-- Bad naming is bad :/
private theorem sub_neg_add:
sub_nat_nat a (b + succ c) = -[1+ c] + sub_nat_nat a b
:= by rw [←neg_coe_succ, add_comm, sub_add_neg']

-- She's a beauty
theorem add_assoc : ∀ {m n k : myint}, m + n + k = m + (n + k)
| (of_nat a) (of_nat b) (of_nat c) :=
by repeat {rw ←coe_nat_eq <|> rw nat_nat_add}; rw mynat.add_assoc
| (of_nat a) (of_nat b) -[1+ c]    :=
by  rw [←coe_nat_eq, ←coe_nat_eq, nat_nat_add, nat_neg_add,
      nat_neg_add, sub_nat_add]
| (of_nat a) -[1+ b]    (of_nat c) :=
by rw [←coe_nat_eq, ←coe_nat_eq, neg_nat_add, nat_neg_add,
      add_comm, ←sub_nat_add, ←sub_nat_add, mynat.add_comm]
| (of_nat a) -[1+ b]    -[1+ c]    :=
by rw [←coe_nat_eq, neg_neg_add, nat_neg_add, nat_neg_add,
  add_comm, ←sub_neg_add, succ_add, add_succ]
| -[1+ a]    (of_nat b) (of_nat c) :=
by rw [←coe_nat_eq, ←coe_nat_eq, neg_nat_add, nat_nat_add,
      neg_nat_add, add_comm, ←sub_nat_add, mynat.add_comm]
| -[1+ a]    (of_nat b) -[1+ c]    :=
by rw [←coe_nat_eq, neg_nat_add, nat_neg_add, ←sub_neg_add,
  add_comm, ←sub_neg_add, succ_add, add_succ, succ_add,
  add_succ, mynat.add_comm]
| -[1+ a]    -[1+ b]    (of_nat c) :=
begin
  rw [←coe_nat_eq, neg_neg_add, neg_nat_add, neg_nat_add,
  ←sub_neg_add, succ_add, add_succ, mynat.add_comm],
end
| -[1+ a]    -[1+ b]    -[1+ c]    :=
by repeat {rw neg_neg_add};
  rw [neg_succ_of_nat_cancel, succ_add, add_succ, mynat.add_assoc]

instance add_is_assoc: is_associative myint add :=
⟨assume a b c, add_assoc⟩

@[simp]
theorem neg_distr: ∀ {m n : myint}, -(m + n) = -m + -n
| (of_nat a) (of_nat b) :=
begin
  rw [←coe_nat_eq, ←coe_nat_eq],
  cases a,
    rw [zz, zero_nat, neg_zero, zero_add, zero_add],
  rw [neg_coe_succ],
  cases b,
    rw [zz, zero_nat, neg_zero, add_zero, add_zero, neg_coe_succ],
  rw [neg_coe_succ, neg_neg_add, nat_nat_add, succ_add, neg_coe_succ,
  neg_succ_of_nat_cancel, add_succ],
end
| (of_nat a) -[1+ b] :=
begin
  rw [←coe_nat_eq, nat_neg_add, neg_neg_succ],
  cases a,
    rw [zz, zero_sub_neg, neg_succ, neg_neg_succ, zero_nat,
        neg_zero, zero_add],
  rw [sub_succ_succ, neg_coe_succ, neg_nat_add, sub_succ_succ,
      sub_nat_nat_switch],
end
| -[1+ a] (of_nat b) :=
begin
  rw [←coe_nat_eq, neg_neg_succ, neg_nat_add],
  cases b,
    rw [zz, zero_sub_neg, neg_succ, neg_neg_succ, zero_nat, neg_zero,
        add_zero],
  rw [sub_succ_succ, neg_coe_succ, nat_neg_add, sub_succ_succ,
      sub_nat_nat_switch],
end
| -[1+ a] -[1+ b] :=
by rw [neg_neg_add, neg_neg_succ, neg_neg_succ, neg_neg_succ,
      nat_nat_add, of_nat_cancel, succ_add, add_succ]

-- Existence is pain
private lemma add_cancel_one: ∀ {m n : myint},
m + 1 = n + 1 → m = n
| (of_nat a) (of_nat b) :=
begin
  rw [←coe_nat_eq, ←coe_nat_eq, ←one_nat, nat_nat_add, nat_nat_add,
      of_nat_cancel, of_nat_cancel],
  assume h,
  apply @add_cancel a b 1,
  rwa [mynat.add_comm, mynat.add_comm 1],
end
| (of_nat a) -[1+ b] :=
begin
  assume h,
  exfalso,
  rw [←coe_nat_eq, ←one_nat, neg_nat_add, one,
      sub_succ_succ, zero_sub_neg, ←one, nat_nat_add] at h,
  cases b,
    rw [zz, neg_of_nat_zero, ←zero_nat, of_nat_cancel,
    mynat.add_comm] at h,
    suffices h1ne0 : 1 ≠ (0:mynat),
      from h1ne0 (add_integral h),
    apply mynat.no_confusion,
  rw [neg_succ] at h,
  from of_nat_ne_neg_succ h,
end
| -[1+ a] (of_nat b) :=
begin
  assume h,
  exfalso,
  rw [←coe_nat_eq, ←one_nat, nat_nat_add, neg_nat_add,
  one, sub_succ_succ, zero_sub_neg, ←one, add_one_succ] at h,
  cases a,
    rw [zz, neg_of_nat_zero, ←zero_nat, of_nat_cancel] at h,
    have : 0 ≠ succ b,
      apply mynat.no_confusion,
    contradiction,
  rw [neg_succ] at h,
  from of_nat_ne_neg_succ h.symm,
end
| -[1+ a] -[1+ b] :=
begin
  rw [←one_nat, neg_nat_add, neg_nat_add, one, sub_succ_succ,
      sub_succ_succ, zero_sub_neg, zero_sub_neg],
  assume h,
  congr,
  rwa [neg_of_nat_cancel] at h,
end

-- Thankfully we can prove this quickly using add_cancel_one
private lemma add_cancel_neg_one: m + -1 = n + -1 → m = n :=
begin
  rw [←neg_cancel, neg_distr, neg_distr, neg_neg],
  assume h,
  have := add_cancel_one h,
  rwa neg_cancel at this,
end

private lemma add_cancel_mp: ∀ k : myint, m + k = n + k → m = n
| (of_nat a) :=
begin
  assume h,
  induction a with a ha,
    rwa [zz, of_nat_zero, add_zero, add_zero] at h,
  {
    rw [of_nat_succ_add_one, ←add_assoc, ←add_assoc] at h,
    have h₁ := add_cancel_one h,
    from ha h₁,
  },
end
| -[1+ a] :=
begin
  assume h,
  induction a with a ha,
    rw [zz, ←neg_one] at h,
    from add_cancel_neg_one h,
  rw [←neg_coe_succ, ←add_one_succ, ←add_one_succ,
  ←nat_nat_add, one_nat, neg_distr_coe_one, ←nat_nat_add,
  one_nat, neg_distr_coe_one, ←@add_assoc m, ←@add_assoc n] at h,
  have h₁ := add_cancel_neg_one h,
  rw [←neg_distr_coe_one, ←one_nat, nat_nat_add, add_one_succ,
  neg_coe_succ] at h₁,
  from ha h₁,
end

-- It's more useful as an iff
@[simp]
theorem add_cancel (k : myint): m + k = n + k ↔ m = n :=
⟨add_cancel_mp k, assume h, by congr; assumption⟩

@[simp]
theorem add_cancel_to_zero: n + m = m ↔ n = 0 :=
by rw [←zero_add m, ←add_assoc, add_cancel, add_zero]

private lemma add_one_neg_one: (1:myint) + -1 = 0 := rfl

@[simp]
theorem self_neg_add: ∀ m : myint, m + (-m) = 0
| (of_nat a) :=
begin
  induction a with a ha,
    rw [zz, of_nat_zero, zero_add, neg_zero],
  rw ←coe_nat_eq at ha,
  rw [←coe_nat_eq, coe_succ, neg_distr_coe_one, add_assoc,
  ←@add_assoc 1, @add_comm 1, @add_assoc (-↑a) 1, add_one_neg_one,
  add_zero, ha],
end
| -[1+ a] :=
by rw [neg_neg_succ, neg_nat_add, sub_succ_succ, sub_self]

@[simp]
theorem neg_self_add : -m + m = 0 := by
rw add_comm; apply self_neg_add

lemma neg_succ_of_succ_add_one: -[1+ succ a] + 1 = -[1+ a] :=
by rw [←one_nat, neg_nat_add, one, sub_succ_succ, zero_sub_neg,
      ←neg_coe_eq_neg_of_nat, neg_coe_succ]

end myint
end hidden
