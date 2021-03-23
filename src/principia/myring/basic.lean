namespace hidden

-- Commutative Unitary Ring
class myring (α : Type) extends has_add α, has_zero α, has_neg α, has_mul α, has_one α :=
(decidable_eq : ∀ a b : α, decidable (a = b))
(add_assoc (a b c : α) : a + b + c = a + (b + c))
(add_zero (a : α) : a + 0 = a)
(add_neg (a : α) : a + -a = 0)
(mul_assoc (a b c : α) : a * b * c = a * (b * c))
(mul_comm (a b : α) : a * b = b * a)
(mul_one (a : α) : a * 1 = a)
(mul_add (a b c : α) : a * (b + c) = a * b + a * c)

namespace myring

variables {α : Type} [myring α] (a b c : α)

instance (a b : α) : decidable (a = b) := decidable_eq a b

theorem one_mul : 1 * a = a :=
begin
  rw [mul_comm],
  from mul_one _,
end

theorem add_mul : (a + b) * c = a * c + b * c :=
by rw [mul_comm, mul_comm _ c, mul_comm _ c, mul_add]

theorem add_cancel_right : a + c = b + c → a = b :=
begin
  assume h,
  rw [←add_zero a, ←add_zero b, ←add_neg c, ←add_assoc, ←add_assoc, h],
end

theorem add_cancel_right_iff: a + c = b + c ↔ a = b :=
begin
  split, {
    from add_cancel_right _ _ _,
  }, {
    assume hbc,
    rw hbc,
  },
end

theorem zero_add : 0 + a = a :=
begin
  apply add_cancel_right _ _ (-a),
  rw [add_assoc, add_neg, add_zero],
end

theorem neg_zero : -(0 : α) = 0 :=
begin
  rw [←zero_add (-(0 : α)), add_neg],
end

private lemma important_first_lemma : a + b = 0 → b + a = 0 :=
begin
  assume h,
  apply add_cancel_right _ _ b,
  rw [add_assoc, h, zero_add, add_zero],
end

theorem neg_add : -a + a = 0 :=
begin
  apply important_first_lemma,
  rw add_neg,
end

theorem add_cancel_left : a + b = a + c → b = c :=
begin
  assume h,
  rw [←zero_add b, ←zero_add c, ←neg_add a, add_assoc, add_assoc, h],
end

theorem add_cancel_left_iff: a + b = a + c ↔ b = c :=
begin
  split, {
    from add_cancel_left _ _ _,
  }, {
    assume hbc, rw hbc,
  },
end

theorem neg_neg : -(-a) = a :=
begin
  apply add_cancel_right _ _ (-a),
  rw [add_neg, neg_add],
end

theorem neg_unique : a + b = 0 ↔ a = -b :=
begin
  split,
    assume h,
    rw [←add_zero a, ←add_neg b, ←add_assoc],
    conv {
      to_rhs,
      rw ←zero_add (-b),
    },
    congr,
    assumption,
  assume h,
  subst h,
  from neg_add b,
end

private theorem neg_distr_swap : -(a + b) = -b + -a :=
begin
  symmetry,
  rw [←neg_unique, add_assoc, ←add_assoc (-a), neg_add, zero_add, neg_add],
end

theorem mul_zero : a * 0 = 0 :=
begin
  apply add_cancel_left (a * 0),
  rw [←mul_add a, zero_add, add_zero],
end

theorem zero_mul : 0 * a = 0 :=
by rw [mul_comm, mul_zero]

theorem neg_eq_mul_neg_one : -a = -1 * a :=
begin
  symmetry,
  conv {
    to_rhs,
    rw ←mul_one a,
  },
  rw [←neg_unique, mul_comm, ←mul_add, neg_add, mul_zero],
end

theorem neg_mul : (-a) * b = -(a * b) :=
begin
  rw [←neg_unique, mul_comm (-a), mul_comm a, ←mul_add, neg_add, mul_zero],
end

theorem mul_neg : a * (-b) = -(a * b) :=
begin
  rw [mul_comm a (-b), mul_comm a b],
  apply neg_mul,
end

theorem neg_mul_neg : (-a) * (-b) = a * b :=
by rw [mul_neg, neg_mul, neg_neg]

theorem neg_distr : -(a + b) = -a + -b :=
by rw [neg_eq_mul_neg_one a, neg_eq_mul_neg_one b, ←mul_add, ←neg_eq_mul_neg_one]

-- "Negate Equality"
theorem neg_eq : a = b ↔ -a = -b :=
begin
  split; assume h,
    congr, assumption,
  rw [←neg_neg a, ←neg_neg b, h],
end

theorem add_comm : a + b = b + a :=
by rw [neg_eq, neg_distr, neg_distr_swap]

theorem add_cancel_left_to_zero : a + b = b → a = 0 :=
begin
  assume h,
  apply add_cancel_right _ _ b,
  rwa zero_add,
end

theorem add_cancel_left_to_zero_iff: a + b = b ↔ a = 0 :=
begin
  split, {
    from add_cancel_left_to_zero _ _,
  }, {
    assume ha0,
    rw ha0,
    rw zero_add,
  },
end

theorem add_cancel_right_to_zero : a + b = a → b = 0 :=
λ h, add_cancel_left_to_zero b a (by rwa add_comm at h)

theorem add_cancel_right_to_zero_iff: a + b = a ↔ b = 0 :=
begin
  split, {
    from add_cancel_right_to_zero _ _,
  }, {
    assume hb0,
    rw hb0,
    rw add_zero,
  },
end

theorem add_left : a = b → c + a = c + b :=
begin
  assume h,
  congr,
  assumption,
end

theorem add_right : a = b → a + c = b + c :=
begin
  assume h,
  congr,
  assumption,
end

theorem one_eq_zero_impl_all_zero : (1 : α) = 0 → ∀ x : α, x = 0 :=
begin
  assume h10,
  intro x,
  rw [←one_mul x, h10, zero_mul],
end

def sub : α → α → α := λ a b, a + (-b)
instance: has_sub α := ⟨sub⟩

theorem sub_def : a - b = a + -b := rfl

theorem sub_self : a - a = 0 :=
begin
  change a + -a = 0,
  apply add_neg,
end

theorem sub_zero : a - 0 = a :=
by rw [sub_def, neg_zero, add_zero]

theorem zero_sub : 0 - a = -a :=
by rw [sub_def, zero_add]

theorem mul_sub : a * (b - c) = a * b - a * c :=
begin
  change a * (b + (-c)) = a * b + -(a * c),
  rw [mul_add, ←mul_neg],
end

theorem neg_sub : -(a - b) = b - a :=
by rw [sub_def, sub_def, neg_distr, neg_neg, add_comm]

theorem sub_mul : (a - b) * c = a * c - b * c:=
by rw [mul_comm, mul_sub, mul_comm a, mul_comm b]

-- This is handy imo
-- Imma have to firmly agree, bro
theorem sub_to_zero_iff_eq : a - b = 0 ↔ a = b :=
begin
  split; assume h, {
    symmetry,
    rwa [neg_eq, ←neg_unique, add_comm],
  }, {
    change a + -b = 0,
    rwa [neg_unique, neg_neg],
  },
end

instance add_is_assoc: is_associative α (+) := ⟨add_assoc⟩
instance add_is_comm: is_commutative α (+) := ⟨add_comm⟩

instance mul_is_assoc: is_associative α (*) := ⟨mul_assoc⟩
instance mul_is_comm: is_commutative α (*) := ⟨mul_comm⟩

end myring

end hidden
