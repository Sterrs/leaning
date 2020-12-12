

namespace hidden

-- Commutative Unitary Ring
class myring (α : Type) extends has_add α, has_zero α, has_neg α, has_mul α, has_one α :=
(add_assoc (a b c : α) : a + b + c = a + (b + c))
(add_zero (a : α) : a + 0 = a)
(add_neg (a : α) : a + -a = 0)
(mul_assoc (a b c : α) : a * b * c = a * (b * c))
(mul_comm (a b : α) : a * b = b * a)
(mul_one (a : α) : a * 1 = a)
(mul_add (a b c : α) : a * (b + c) = a * b + a * c)

namespace myring

variables {α : Type} [myring α] (a b c : α)

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

private theorem neg_eq_mul_neg_one : -a = -1 * a :=
begin
  symmetry,
  conv {
    to_rhs,
    rw ←mul_one a,
  },
  rw [←neg_unique, mul_comm, ←mul_add, neg_add, mul_zero],
end

theorem neg_mul : -(a * b) = (-a) * b :=
begin
  symmetry,
  rw [←neg_unique, mul_comm (-a), mul_comm a, ←mul_add, neg_add, mul_zero],
end

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

theorem test : a * b + b = (a + 1) * b :=
begin
  conv {
    to_lhs,
    congr,
      skip,
    rw [←one_mul b],
  },
  rw ←add_mul,
end

end myring

end hidden
