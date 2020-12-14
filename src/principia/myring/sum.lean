import ..sequence
import .basic
import ..mynat.induction

namespace hidden
namespace myring

open sequence
open myring

variables {α : Type} [myring α]
variables a b c d : α
variables m n k : mynat
variables term f g : sequence α

@[simp] theorem sum_zero: sum term 0 = 0 := rfl

@[simp]
theorem sum_succ: sum term (mynat.succ n) = sum term n + term n := rfl

@[simp]
theorem sum_one: sum term 1 = term 0 :=
begin
  change 0 + term 0 = term 0,
  rw zero_add,
end

@[simp] theorem prod_zero: product term 0 = 1 := rfl

@[simp]
theorem prod_succ:
product term (mynat.succ n) = product term n * term n := rfl

@[simp]
theorem prod_one: product term 1 = term 0 :=
begin
  change 1 * term 0 = term 0,
  rw one_mul,
end

-- theorem constant_sum: ∀ n : mynat, sum ↑(1 : α) n = n
-- | zero := rfl
-- | (succ n) := by rw [sum_succ, constant_sum, coe_triv, add_one_succ]

theorem mul_sum: ∀ n, sum (↑a * f) n = a * (sum f n)
| mynat.zero     := begin
  rw mynat.zz,
  change (↑a * f).sum 0 = a * 0,
  rw mul_zero,
  refl,
end
| (mynat.succ n) := by rw [sum_succ, sum_succ, mul_add, mul_sum, coe_mul]

theorem sum_distr: ∀ n, sum (f + g) n = (sum f n) + (sum g n)
| mynat.zero     := begin
  rw mynat.zz,
  change 0 = 0 + (0 : α),
  rw add_zero,
end
| (mynat.succ n) := by conv {
  rw [sum_succ, sum_succ, sum_succ, sum_distr, addition],
  to_rhs,
  rw [←add_assoc, add_assoc (sum f n), add_comm (f n),
      ←add_assoc (sum f n), add_assoc],
}

theorem sum_cancel: (∀ n, sum f n = sum g n) ↔ ∀ n, f n = g n :=
begin
  split, {
    assume h,
    intro n,
    have hsn := h (mynat.succ n),
    repeat {rw sum_succ at hsn},
    rw h n at hsn,
    apply add_cancel_left (g.sum n),
    assumption,
  }, {
    assume h n,
    induction n with n hn,
      refl,
    rw [sum_succ, sum_succ, hn, h n],
  },
end

theorem apply_sum: (∀ n, f n = g n) → sum f k = sum g k :=
begin
  assume h,
  induction k with k hk,
    refl,
  rw [sum_succ, sum_succ, h k, hk],
end

theorem sum_tail:
sum f (mynat.succ n) = sum (λ k, f (mynat.succ k)) n + f 0 :=
begin
  induction n, {
    rw sum_succ,
    simp,
  }, {
    rw [sum_succ, n_ih, add_assoc, add_comm (f 0), ←add_assoc,
        ←sum_succ],
  },
end

private theorem restricted_mpr {m : mynat} {f g : sequence α}
(h : ∀ n, n < m → f n = g n) : ∀ n, n ≤ m → sum f n = sum g n
| mynat.zero := λ _, rfl
| (mynat.succ n) := (assume hnm, by rw [sum_succ, sum_succ,
  restricted_mpr n (@mynat.le_cancel_strong n m 1 hnm),
  h n (mynat.lt_iff_succ_le.mpr hnm)])

-- this might be necessary/useful when working with -, since it lets
-- you basically assume k < n in order to rewrite the terms
theorem sum_cancel_restricted: (∀ n, n ≤ m → sum f n = sum g n) ↔
(∀ n, n < m → f n = g n) := ⟨assume h n hnm,
have hsn : _ := h (mynat.succ n) (mynat.lt_iff_succ_le.mp hnm),
by {rw [sum_succ, sum_succ, h n (mynat.lt_impl_le hnm)] at hsn,
    from add_cancel_left _ _ _ hsn},
restricted_mpr⟩

private theorem add_two: ∀ k, k + 2 = mynat.succ (mynat.succ k) := (λ k, rfl)

theorem sum_reverse:
sum f n = sum (λ k, f (n - mynat.succ k)) n :=
begin
  have cancel_f:
    ∀ n k: mynat, ∀ f: sequence α,
      n = k → f n = f k, {
    intros n k f,
    assume h,
    rw h,
  },
  revert n f,
  -- easy way to access the n - 2 case of IH
  apply duo_induction
    (λ n, ∀ f, sum f n =
      sum (λ k, f (n - mynat.succ k)) n), {
    intro f,
    refl,
  }, {
    intro f,
    refl,
  }, {
    intro n,
    assume h_ih _,
    intro f,
    rw [add_two, sum_succ, sum_tail, h_ih,
        sum_succ, sum_tail, mynat.sub_succ_succ,
        mynat.sub_zero, mynat.sub_self_eq_zero],
    conv {
      congr,
      rw [add_assoc, add_comm],
      skip,
      rw [add_assoc, add_comm],
      congr,
      rw add_comm,
    },
    apply add_left,
    -- help lean with type inference a bit
    have h_aesthetic := @mynat.le_refl n,
    revert h_aesthetic,
    apply (sum_cancel_restricted _ _ _).mpr,
    intro m,
    assume hmn,
    apply cancel_f,
    rw [mynat.sub_succ_succ, mynat.sub_succ_succ],
    cases mynat.sub_succ_converse hmn with d hd,
    symmetry,
    rw [mynat.sub_succ_rearrange, mynat.sub_succ, hd, mynat.succ_sub_one],
    from mynat.sub_succ_rearrange.mp hd,
  },
end

-- TODO: general theorem about sum f (n * m) as a double sum?
theorem sum_split:
sum f (2 * n) = sum f n + sum (λ k, f (n + k)) n :=
begin
  induction n with n hn, {
    rw [mynat.zz, mynat.mul_zero],
    dsimp only [sequence.sum],
    rw add_zero,
  }, {
    rw mynat.mul_succ,
    rw mynat.add_comm 2,
    have: sum f (2 * n + 2) = sum f (2 * n) + f (2 * n) + f (2 * n + 1) := rfl,
    rw this, clear this,
    rw hn,
    have: f (2 * n) + f (2 * n + 1) = f (n + n) + f (n + mynat.succ n), {
      repeat {rw mynat.mul_comm 2},
      refl,
    },
    rw add_assoc,
    rw this,
    rw add_assoc,
    conv {
      congr, congr, skip,
      rw ←add_assoc,
      rw ←sum_succ,
      rw ←sum_succ,
      rw sum_tail,
      rw add_comm,
    },
    rw ←add_assoc,
    rw mynat.add_zero,
    rw ←sum_succ,
    have: ∀ k, f (n + mynat.succ k) = f(mynat.succ n + k), {
      simp,
    },
    rw (sum_cancel _ _).mpr this,
  },
end

theorem prod_tail:
product f (mynat.succ n) = product (λ k, f (mynat.succ k)) n * f 0 :=
begin
  induction n with n hn, {
    refl,
  }, {
    rw prod_succ,
    rw hn,
    rw mul_assoc,
    rw mul_comm (f 0),
    rw ←mul_assoc,
    rw ←prod_succ,
  },
end

theorem prod_congr:
(∀ k, f k = g k) → (∀ n, product f n = product g n) :=
begin
  assume heq,
  intro n,
  induction n with n hn, {
    refl,
  }, {
    repeat {rw prod_succ},
    rw hn,
    rw heq n,
  },
end

theorem prod_split:
product f (2 * n) = product f n * product (λ k, f (n + k)) n :=
begin
  induction n with n hn, {
    rw [mynat.zz, mynat.mul_zero],
    dsimp only [sequence.product],
    rw mul_one,
  }, {
    rw mynat.mul_succ,
    rw mynat.add_comm 2,
    have: product f (2 * n + 2) = product f (2 * n) * f (2 * n) * f (2 * n + 1) := rfl,
    rw this, clear this,
    rw hn,
    have: f (2 * n) * f (2 * n + 1) = f (n + n) * f (n + mynat.succ n), {
      repeat {rw mynat.mul_comm 2},
      refl,
    },
    rw mul_assoc,
    rw this,
    rw mul_assoc,
    conv {
      congr, congr, skip,
      rw ←mul_assoc,
      rw ←prod_succ,
      rw ←prod_succ,
      rw prod_tail,
      rw mul_comm,
    },
    rw ←mul_assoc,
    rw mynat.add_zero,
    rw ←prod_succ,
    have: ∀ k, f (n + mynat.succ k) = f(mynat.succ n + k), {
      simp,
    },
    rw prod_congr _ _ this,
  },
end

end myring
end hidden
