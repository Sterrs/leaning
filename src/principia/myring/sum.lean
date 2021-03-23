import ..sequence
import .basic
import ..mynat.induction
import ..mynat.nat_sub

namespace hidden
namespace myring

open sequence
open myring

variables {α : Type} [myring α]
variables a b c d : α
variables m n k : mynat
variables term f g : sequence α
variables (op: α → α → α) (dflt: α)

@[simp] theorem sum_zero: sum term 0 = 0 := rfl

@[simp]
theorem sum_succ: sum term (mynat.succ n) = sum term n + term n := rfl

@[simp]
theorem sum_one: sum term 1 = term 0 :=
begin
  apply zero_add,
end

@[simp] theorem prod_zero: product term 0 = 1 := rfl

@[simp]
theorem prod_succ:
product term (mynat.succ n) = product term n * term n := rfl

@[simp]
theorem prod_one: product term 1 = term 0 :=
begin
  apply one_mul,
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

theorem apply_accumulate:
(∀ n, f n = g n) → accumulate op dflt f k = accumulate op dflt g k :=
begin
  assume h,
  induction k with k hk, {
    refl,
  }, {
    dsimp [accumulate],
    rw h,
    rw hk,
  },
end

theorem apply_sum:
(∀ n, f n = g n) → sum f k = sum g k :=
λ h, apply_accumulate k f g (+) 0 h

theorem apply_prod:
(∀ n, f n = g n) → product f k = product g k :=
λ h, apply_accumulate k f g (*) 1 h

theorem accumulate_tail
[hcomm: is_commutative _ op]
[hassoc: is_associative _ op]:
accumulate op dflt f (mynat.succ n) =
op (accumulate op dflt (λ k, f (mynat.succ k)) n) (f 0) :=
begin
  induction n with n hn, {
    refl,
  }, {
    unfold accumulate at *,
    rw hn,
    ac_refl,
  },
end

theorem sum_tail:
sum f (mynat.succ n) = sum (λ k, f (mynat.succ k)) n + f 0 :=
accumulate_tail n f (+) 0

theorem prod_tail:
product f (mynat.succ n) = product (λ k, f (mynat.succ k)) n * f 0 :=
accumulate_tail n f (*) 1

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
    congr,
    rw [mynat.sub_succ_succ, mynat.sub_succ_succ],
    cases mynat.sub_succ_converse hmn with d hd,
    symmetry,
    rw [mynat.sub_succ_rearrange, mynat.sub_succ, hd, mynat.succ_sub_one],
    from mynat.sub_succ_rearrange.mp hd,
  },
end

theorem sum_split:
sum f (n + m) = sum f n + sum (λ k, f (n + k)) m :=
begin
  induction m with m hm, {
    symmetry,
    from add_zero _,
  }, {
    rw mynat.add_succ,
    rw sum_succ,
    rw hm,
    rw sum_succ,
    rw add_assoc,
  },
end

theorem sum_split_lots:
sum f (n * m) =
sum (λ k, sum (λ ℓ, f (ℓ + k * n)) n) m :=
begin
  induction m with m ih_m generalizing f, {
    refl,
  }, {
    rw mynat.mul_succ,
    rw sum_split,
    conv {
      to_lhs,
      rw add_comm,
      congr,
      rw ih_m _,
    },
    rw sum_tail,
    apply congr, {
      apply congr, refl,
      apply (sum_cancel _ _).mpr,
      intro k,
      apply (sum_cancel _ _).mpr,
      intro ℓ,
      rw mynat.succ_mul,
      ac_refl,
    }, {
      apply (sum_cancel _ _).mpr,
      intro ℓ,
      rw mynat.zero_mul,
      refl,
    },
  },
end

theorem sum_square_limit_swap
(f: mynat → mynat → α):
sum (λ k, sum (λ ℓ, f k ℓ) n) m =
sum (λ ℓ, sum (λ k, f k ℓ) m) n :=
begin
  induction m with m ih_m, {
    conv {
      to_lhs,
      change (0: α),
    },
    induction n with n ih_n, {
      refl,
    }, {
      symmetry,
      rw ih_n,
      from add_zero _,
    },
  }, {
    rw sum_succ,
    rw ih_m,
    clear ih_m,
    induction n with n ih_n, {
      from add_zero _,
    }, {
      conv {
        to_rhs,
        rw sum_succ,
        rw ←ih_n,
      },
      repeat {rw sum_succ},
      repeat {rw add_assoc},
      apply congr, refl,
      rw add_comm,
      repeat {rw add_assoc},
      apply congr, refl,
      from add_comm _ _,
    },
  },
end

theorem sum_triangle_limit_swap
(f: mynat → mynat → α):
sum (λ k, sum (λ ℓ, f k ℓ) k.succ) n =
sum (λ ℓ, sum (λ k, f (k + ℓ) ℓ) (n - ℓ)) n :=
begin
  induction n with n ih_n, {
    refl,
  }, {
    rw sum_succ,
    rw ih_n, clear ih_n,
    rw sum_succ,
    rw sum_succ,
    rw mynat.succ_sub_self,
    repeat {rw ←add_assoc},
    apply congr, {
      apply congr, refl,
      rw ←sum_distr,
      apply (sum_cancel_restricted n _ _).mpr, {
        intro ℓ,
        assume hln,
        have: n.succ - ℓ = (n - ℓ).succ, {
          cases mynat.sub_succ_converse hln with w hw,
          rw hw,
          rw mynat.sub_succ_rearrange at hw,
          rw hw,
          rw ←mynat.succ_add,
          rw mynat.add_sub,
        },
        rw this, clear this,
        rw sum_succ,
        dsimp only [],
        conv {
          to_lhs,
          change (sum (λ (k : mynat), f (k + ℓ) ℓ) (n - ℓ) + f n ℓ),
        },
        apply congr, {
          refl,
        }, {
          rw mynat.sub_add_condition.mpr (mynat.lt_impl_le hln),
        },
      }, {
        refl,
      },
    }, {
      conv {
        to_rhs,
        change 0 + f (0 + n) n,
      },
      rw zero_add,
      rw mynat.zero_add,
    },
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

end myring
end hidden
