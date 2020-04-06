import .mylist
import ..mynat.nat_sub

-- Sorting algorithms on lists of naturals
-- can probably be generalised to some type class thing

-- TODO: encode/state criterion for a sorting algorithm to
-- be stable, and prove it
-- more algorithms, obviously

namespace hidden

open mynat

universe u
variable {T: Sort u}
variables {a b c d m n k x y z: mynat}
variables {lst lst1 lst2 lst3 xs ys zs: mylist mynat}
variables {alg: mylist mynat → mylist mynat}

def is_sorted (lst: mylist mynat): Prop :=
∀ a b: mynat,
  ∀ hbl: b < len lst,
    ∀ hab: a < b,
      get a lst (lt_trans hab hbl) ≤
        get b lst hbl

def count [decidable_eq T]: T → mylist T → mynat
| _ []        := 0
| x (y :: ys) := if x = y then
                 succ (count x ys) else
                 count x ys

-- this seems more straightforward than using bijections or something.
-- correct me if I'm wrong
def is_perm (lst1 lst2: mylist mynat) :=
∀ m: mynat,
  count m lst1 = count m lst2

def sort_alg_correct (alg: mylist mynat → mylist mynat) :=
∀ lst: mylist mynat,
  is_sorted (alg lst) ∧ is_perm lst (alg lst)

private theorem succ_lt_impl_lt: succ a < n → a < n :=
@lt_cancel_strong a n 1

theorem adjacent_sorted_implies_sorted:
(∀ a,
  ∀ hsal: succ a < len lst,
    get a lst (succ_lt_impl_lt hsal) ≤
    get (succ a) lst hsal)
→ is_sorted lst :=
begin
  assume hadj,
  intros a b hbl hab,
  rw lt_iff_succ_le at hab,
  cases hab with d hd,
  induction d with d d_ih generalizing b, {
    conv in b {rw hd},
    simp,
    apply hadj,
  }, {
    conv in b {rw hd},
    conv in (succ a + succ d) {rw add_succ},
    have := d_ih _ _ _ rfl,
    apply le_trans this (hadj _ _),
    rw lt_iff_succ_le,
    from le_to_add,
  },
end

theorem empty_sorted: is_sorted [] :=
begin
  intros a b,
  assume hbl hab,
  exfalso,
  from lt_nzero hbl,
end

theorem singleton_sorted: is_sorted [x] :=
begin
  intros a b,
  assume hbl hab,
  exfalso,
  dsimp [len] at hbl,
  rw [←one_eq_succ_zero, ←le_iff_lt_succ] at hbl,
  rw le_zero hbl at hab,
  from lt_nzero hab,
end

theorem cons_sorted:
x ≤ y → is_sorted (y :: ys) → is_sorted (x :: y :: ys) :=
begin
  assume hxy hstd_yys,
  apply adjacent_sorted_implies_sorted,
  intro m,
  assume hsal,
  cases m, {
    from hxy,
  }, {
    have hsm := lt_succ_cancel hsal,
    have hmsm := @lt_to_add_succ m 0,
    have := hstd_yys m (succ m) hsm hmsm,
    from this,
  },
end

theorem duo_sorted: x ≤ y → is_sorted (x :: y :: []) :=
(λ h, cons_sorted h singleton_sorted)

theorem tail_sorted: is_sorted (x :: xs) → is_sorted xs :=
begin
  assume hstd_xxs,
  intros a b,
  assume hbl hab,
  have := hstd_xxs (succ a) (succ b)
                   (@lt_add _ _ 1 hbl)
                   (@lt_add _ _ 1 hab),
  from this, -- too lazy to change indentation
end

theorem empty_perm: is_perm [] [] :=
begin
  intro m,
  refl,
end

theorem singleton_perm: is_perm [x] [x] :=
begin
  intro m,
  refl,
end

theorem perm_refl: is_perm lst lst :=
begin
  intro m,
  refl,
end

theorem perm_symm:
is_perm lst1 lst2 → is_perm lst2 lst1 :=
begin
  assume hp12,
  intro m,
  symmetry,
  from hp12 m,
end

theorem cons_perm:
is_perm xs ys → is_perm (x :: xs) (x :: ys) :=
begin
  assume hpxsys,
  intro m,
  dsimp [count],
  cases (@lem_nat_eq m x) with hmx hmnx, {
    repeat {rw if_pos hmx},
    rw hpxsys m,
  }, {
    repeat {rw if_neg hmnx},
    from hpxsys m,
  },
end

theorem perm_trans:
is_perm lst1 lst2 → is_perm lst2 lst3 → is_perm lst1 lst3 :=
begin
  assume hp12 hp23,
  intro m,
  from eq.trans (hp12 m) (hp23 m),
end

theorem count_empty: count x [] = 0 := rfl

theorem empty_perm_is_empty:
is_perm lst [] → lst = [] :=
begin
  assume hple,
  cases lst, {
    refl,
  }, {
    exfalso,
    have := hple lst_head,
    dsimp [count] at this,
    rw if_pos rfl at this,
    from succ_ne_zero this,
  },
end

theorem count_concat:
count m (lst1 ++ lst2)
  = count m lst1 + count m lst2 :=
begin
  induction lst1 with x xs h_ih, {
    rw [count_empty, zero_add, empty_concat],
  }, {
    dsimp [count],
    cases (@lem_nat_eq m x) with hmx hmnx, {
      repeat {rw if_pos hmx},
      rw [h_ih, succ_add],
    }, {
      repeat {rw if_neg hmnx},
      from h_ih,
    },
  },
end

theorem perm_concat:
is_perm xs ys → is_perm lst1 lst2
  → is_perm (xs ++ lst1) (ys ++ lst2) :=
begin
  assume hpxsys hp12,
  intro m,
  rw [count_concat, count_concat, hpxsys m, hp12 m],
end

theorem duo_perm:
is_perm (x :: y :: []) (y :: x :: []) :=
begin
  intro m,
  dsimp [count],
  cases (@lem_nat_eq m x) with hmx hmnx, {
    repeat {rw if_pos hmx},
    cases (@lem_nat_eq m y) with hmy hmny, {
      repeat {rw if_pos hmy},
    }, {
      repeat {rw if_neg hmny},
      refl,
    },
  }, {
    repeat {rw if_neg hmnx},
    cases (@lem_nat_eq m y) with hmy hmny, {
      repeat {rw if_pos hmy},
      refl,
    }, {
      repeat {rw if_neg hmny},
    },
  },
end

-- insertion sort

def insert_aux: mynat → mylist mynat → mylist mynat
| x []        := [x]
| x (y :: ys) := if x ≤ y then
                 x :: y :: ys else
                 y :: insert_aux x ys

def insertion_sort: mylist mynat → mylist mynat
| []        := []
| (x :: xs) := insert_aux x (insertion_sort xs)

-- ew
theorem insertion_preserves_sorted:
is_sorted lst → is_sorted (insert_aux x lst) :=
begin
  induction lst with y ys h_ih, {
    assume _,
    from singleton_sorted,
  }, {
    assume h,
    dsimp [insert_aux],
    cases le_lem x y with hxy hnxy, {
      rw if_pos hxy,
      from cons_sorted hxy h,
    }, {
      rw if_neg hnxy,
      cases hz: insert_aux x ys with z zs, {
        from singleton_sorted,
      }, {
        apply cons_sorted, {
          cases ys with y' ys, {
            have: x = z, {
              dsimp [insert_aux] at hz,
              from cons_injective_1 hz,
            },
            rw ←this,
            from lt_impl_le hnxy,
          }, {
            dsimp [insert_aux] at hz,
            cases (le_lem x y') with hxy' hnxy', {
              rw if_pos hxy' at hz,
              rw ←(cons_injective_1 hz),
              from lt_impl_le hnxy,
            }, {
              rw if_neg hnxy' at hz,
              rw ←(cons_injective_1 hz),
              apply h 0 1 _ _, {
                dsimp [len],
                apply @lt_add _ _ 1,
                from zero_lt_succ,
              }, {
                from zero_lt_succ,
              },
            },
          },
        }, {
          rw ←hz,
          apply h_ih,
          from tail_sorted h,
        },
      },
    },
  },
end

theorem insertion_sort_is_sorted:
is_sorted (insertion_sort lst) :=
begin
  induction lst with head tail h_ih, {
    dsimp [insertion_sort],
    from empty_sorted,
  }, {
    dsimp [insertion_sort],
    from insertion_preserves_sorted h_ih,
  },
end

theorem insertion_is_perm:
is_perm (x :: xs) (insert_aux x xs) :=
begin
  induction xs with x' xs h_ih, {
    from singleton_perm,
  }, {
    dsimp [insert_aux],
    cases (le_lem x x') with hxx' hnxx', {
      rw if_pos hxx',
      from perm_refl,
    }, {
      rw if_neg hnxx',
      apply perm_trans _ (cons_perm h_ih),
      from perm_concat duo_perm perm_refl,
    },
  },
end

theorem insertion_sort_is_perm:
is_perm lst (insertion_sort lst) :=
begin
  induction lst with head tail h_ih, {
    from empty_perm,
  }, {
    dsimp [insertion_sort],
    have := @cons_perm head _ _ h_ih,
    from perm_trans this insertion_is_perm,
  },
end

theorem insertion_sort_correct:
sort_alg_correct insertion_sort :=
(λ lst,
  and.intro
    insertion_sort_is_sorted insertion_sort_is_perm)

theorem perm_len:
is_perm lst1 lst2 → len lst1 = len lst2 :=
begin
  sorry,
end

theorem is_perm_sorted_eq:
sort_alg_correct alg
  → is_perm lst1 lst2
    → alg lst1 = alg lst2 :=
begin
  sorry,
end

end hidden
