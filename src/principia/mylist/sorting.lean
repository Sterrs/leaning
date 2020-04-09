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

theorem empty_perm: is_perm [] [] := (λ _, rfl)

theorem singleton_perm: is_perm [x] [x] := (λ _, rfl)

theorem perm_refl: is_perm lst lst := (λ _, rfl)

theorem perm_symm:
is_perm lst1 lst2 → is_perm lst2 lst1 :=
(λ hp12 m, (hp12 m).symm)

theorem cons_perm:
is_perm xs ys → is_perm (x :: xs) (x :: ys) :=
begin
  assume hpxsys,
  intro m,
  dsimp [count],
  rw hpxsys m,
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
    by_cases (m = x), {
      repeat {rw if_pos h},
      rw [h_ih, succ_add],
    }, {
      repeat {rw if_neg h},
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
  by_cases hmx: m = x, {
    repeat {rw if_pos hmx},
    by_cases hmy:m = y, {
      repeat {rw if_pos hmy},
    }, {
      repeat {rw if_neg hmy},
      refl,
    },
  }, {
    repeat {rw if_neg hmx},
    by_cases hmy: m = y, {
      repeat {rw if_pos hmy},
      refl,
    }, {
      repeat {rw if_neg hmy},
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
    by_cases hxy: x ≤ y, {
      rw if_pos hxy,
      from cons_sorted hxy h,
    }, {
      rw if_neg hxy,
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
            from lt_impl_le hxy,
          }, {
            dsimp [insert_aux] at hz,
            by_cases hxy': x ≤ y', {
              rw if_pos hxy' at hz,
              rw ←(cons_injective_1 hz),
              from lt_impl_le hxy,
            }, {
              rw if_neg hxy' at hz,
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
    by_cases hxx': x ≤ x', {
      rw if_pos hxx',
      from perm_refl,
    }, {
      rw if_neg hxx',
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

-- more theory about permutations/sorted lists

theorem perm_concat_swap:
is_perm (xs ++ ys) (ys ++ xs) :=
begin
  intro m,
  rw count_concat,
  rw count_concat,
  rw add_comm,
end

theorem rev_perm: is_perm lst (rev lst) :=
begin
  induction lst with head tail h_ih, {
    from empty_perm,
  }, {
    from perm_trans
          (cons_perm h_ih)
          (@perm_concat_swap [head] (rev tail)),
  },
end

-- is switching away from recursive definitions a good idea? who knows

def slice:
  Π m n: mynat,
    Π lst: mylist T,
      m ≤ n →
        n ≤ len lst → mylist T :=
(λ m n lst hmn hnl,
  -- really I just want to use the witness to m ≤ n here
  take (n - m)
    (drop m lst (le_trans hmn hnl))
    begin
      cases hmn with d hd,
      conv in n {rw hd},
      rw add_comm,
      rw add_sub,
      apply @le_cancel _ _ m,
      rw len_drop,
      rw add_comm,
      rw ←hd,
      from hnl,
    end)

-- swap elements at two indices (m and n resp.) in a list.
-- Cannot be the same index.
-- Require one index less than the other for convenience.
-- maybe define wrapper function?? but makes proofs harder
def swap_elems:
Π (m n: mynat) (lst: mylist T), m < n → n < len lst → mylist T
:= (λ m n lst hmn hnl,
    take m lst (lt_impl_le (lt_trans hmn hnl))
    ++ [get n lst hnl]
    ++ slice (succ m) n lst (lt_iff_succ_le.mp hmn)
                            (lt_impl_le hnl)
    ++ [get m lst (lt_trans hmn hnl)]
    ++ drop (succ n) lst (lt_iff_succ_le.mp hnl))

theorem len_slice
(hmn: m ≤ n)
(hnl: n ≤ len lst):
len (slice m n lst hmn hnl) + m = n :=
begin
  unfold slice,
  rw len_take,
  cases hmn with d hd,
  rw hd,
  rw add_comm m d,
  rw add_sub,
end

theorem len_swap
(hmn: m < n)
(hnl: n < len lst):
len (swap_elems m n lst hmn hnl) = len lst :=
begin
  unfold swap_elems,
  repeat {rw len_concat_add},
  rw len_take,
  rw len_singleton,
  rw len_singleton,
  conv {
    congr,
    congr,
    congr,
    rw add_one_succ,
    rw add_comm,
    rw len_slice,
  },
  rw add_one_succ,
  rw add_comm,
  rw len_drop,
end

-- TODO: all this hypothesis-slinging is getting a bit ugly

-- good god working with equivalence relations is a pain
theorem swap_perm
(hmn: m < n)
(hnl: n < len lst):
is_perm lst (swap_elems m n lst hmn hnl) :=
begin
  have hml := lt_trans hmn hnl,
  have hml_ns := lt_impl_le hml,
  have hnl_ns := lt_impl_le hnl,
  unfold swap_elems,
  conv {
    congr,
    rw ←take_concat_drop hml_ns hml_ns,
  },
  repeat {rw concat_assoc},
  apply perm_concat perm_refl,
  have hdmlne: drop m lst hml_ns ≠ [], {
    assume h,
    have h2: len lst = m, {
      rw ←@len_drop _ _ m,
      rw h,
      from zero_add m,
    },
    rw h2 at hml,
    from lt_nrefl hml,
  },
  have hrw := @cons_head_tail _ (drop m lst hml_ns) hdmlne,
  have hrw2 := get_head_drop hml_ns hml hdmlne,
  conv {
    congr,
    rw ←hrw,
    rw ←hrw2,
  }, clear hrw hrw2,
  apply perm_trans _ perm_concat_swap,
  apply
    @perm_trans _
      (tail (drop m lst hml_ns) hdmlne ++ [get m lst hml])
      _ perm_concat_swap,
  unfold slice,
  rw ←@drop_one_tail _ (drop m lst hml_ns)
    begin
      cases drop m lst hml_ns, {
        contradiction,
      }, {
        apply succ_le_succ,
        from zero_le,
      },
    end,
  rw @drop_drop _ _ m 1 _ _ (lt_iff_succ_le.mp hml),
  conv in (m + 1) {rw add_one_succ},
  have hdl:
    ∀ hsml: succ m ≤ len lst,
      n - succ m ≤ len (drop (succ m) lst hsml), {
    assume _,
    cases (lt_iff_succ_le.mp hmn) with k hk,
    rw hk,
    rw add_comm,
    rw add_sub,
    apply @le_cancel _ _ (succ m),
    rw len_drop,
    rw add_comm,
    rw ←hk,
    from lt_impl_le hnl,
  },
  conv {
    congr,
    congr,
    rw ←@take_concat_drop _ (drop (succ m) lst _) (n - succ m) (hdl _) (hdl _),
  },
  rw concat_assoc,
  rw concat_assoc,
  apply perm_concat perm_refl,
  have hrw:
      succ m + (n - succ m) = n, {
    cases (lt_iff_succ_le.mp hmn) with k hk,
    rw hk,
    rw add_comm _ k,
    rw add_sub,
    rw add_comm,
  },
  rw @drop_drop _ lst (succ m) (n - succ m)
                (lt_iff_succ_le.mp hml) (hdl _)
                (hrw.symm ▸ lt_impl_le hnl),
  conv {
    congr,
    congr,
    congr,
    rw hrw,
  },
  have hdnlne: drop n lst hnl_ns ≠ [], {
    assume h,
    have h2: len lst = n, {
      rw ←@len_drop _ _ n,
      rw h,
      from zero_add n,
    },
    rw h2 at hnl,
    from lt_nrefl hnl,
  },
  have hrw2 := @cons_head_tail _ (drop n lst hnl_ns) hdnlne,
  have hrw3 := @get_head_drop _ lst n hnl_ns hnl hdnlne,
  conv {
    congr,
    congr,
    rw ←hrw2,
    rw ←hrw3,
  },
  apply perm_trans perm_concat_swap,
  rw concat_assoc,
  apply perm_concat perm_refl,
  apply perm_trans _ perm_concat_swap,
  apply @perm_concat _ _ [get n lst hnl] _ perm_refl,
  rw ←@drop_one_tail _ (drop n lst hnl_ns)
    begin
      cases drop n lst hnl_ns, {
        contradiction,
      }, {
        apply succ_le_succ,
        from zero_le,
      },
    end,
  rw @drop_drop _ _ n 1 _ _ (lt_iff_succ_le.mp hnl),
  from perm_refl,
end

-- TODO: swap involutive, get_swap

theorem count_head_eq:
count x (x :: xs) = succ (count x xs) :=
begin
  unfold count,
  rw if_pos rfl,
end

-- again should be typeclass
-- also this kind of signals how useless ∈ was
def index:
Π (n: mynat) (lst: mylist mynat), count n lst ≠ 0 → mynat
| n []        h := absurd count_empty h
| n (x :: xs) h := if hnx: n = x then
                   0 else
                   succ (index n xs
                    begin
                      unfold count at h,
                      rw if_neg hnx at h,
                      from h,
                    end)

theorem index_head_eq
(hc: count x (x :: xs) ≠ 0):
index x (x :: xs) hc = 0 := dif_pos rfl

theorem index_valid
(hc: count n lst ≠ 0):
index n lst hc < len lst :=
begin
  induction lst with head tail h_ih, {
    contradiction,
  }, {
    unfold index,
    by_cases hnh: n = head, {
      rw dif_pos hnh,
      from zero_lt_succ,
    }, {
      rw dif_neg hnh,
      from succ_lt_succ (h_ih _),
    },
  },
end

@[simp]
theorem get_index
(hc: count n lst ≠ 0)
(hil: index n lst hc < len lst):
get (index n lst hc) lst hil = n :=
begin
  induction lst with head tail h_ih, {
    contradiction,
  }, {
    unfold index,
    by_cases hnh: n = head, {
      conv {
        congr,
        congr,
        rw dif_pos hnh,
      },
      rw get_zero_cons,
      from hnh.symm,
    }, {
      conv {
        congr,
        congr,
        rw dif_neg hnh,
      },
      rw get_succ_cons,
      apply h_ih,
    },
  },
end

theorem perm_head_cancel:
is_perm (x :: xs) (x :: ys) → is_perm xs ys :=
begin
  assume hpxsys,
  intro m,
  have := hpxsys m,
  unfold count at this,
  by_cases hmx: m = x, {
    repeat {rw if_pos hmx at this},
    from succ_inj this,
  }, {
    repeat {rw if_neg hmx at this},
    from this,
  },
end

theorem perm_concat_cancel:
is_perm (xs ++ lst1) (xs ++ lst2) → is_perm lst1 lst2 :=
begin
  induction xs with x xs h_ih, {
    assume h,
    from h,
  }, {
    assume h,
    apply h_ih,
    from perm_head_cancel h,
  },
end

theorem perm_len:
is_perm lst1 lst2 → len lst1 = len lst2 :=
begin
  induction lst1 with x xs h_ih generalizing lst2, {
    assume h,
    rw empty_perm_is_empty (perm_symm h),
  }, {
    assume h,
    cases lst2 with y ys, {
      cases empty_perm_is_empty h,
    }, {
      by_cases hxy: x = y, {
        rw hxy at h,
        -- can't work out direct way to "cancel" succs in goal
        simp,
        apply h_ih,
        from perm_head_cancel h,
      }, {
         have h_aux_1: count x (y :: ys) ≠ 0, {
          rw ←h x,
          rw count_head_eq,
          from succ_ne_zero,
         },
         have h_aux_2: 0 < index x (y :: ys) h_aux_1, {
          unfold index,
          rw dif_neg hxy,
          from zero_lt_succ,
         },
        -- world record for biggest "have" type-to-value ratio
        -- thank your maker that I split away some of the
        -- auxiliary hypotheses
        -- also I had to in order to do "cases" with hypothesis later,
        -- so couldn't afford to have any _s lying around
        have hpswap:
          is_perm
            (y :: ys)
            (swap_elems
              0
              (index x (y :: ys) h_aux_1)
              (y :: ys)
              h_aux_2
              (index_valid h_aux_1)) := swap_perm _ _,
        have hxswap := perm_trans h hpswap,
        clear hpswap,
        cases
            hswap: swap_elems 0 (index x (y :: ys) h_aux_1) (y :: ys) h_aux_2 (index_valid h_aux_1)
            with swap_head swap_tail, {
          rw hswap at hxswap,
          cases (empty_perm_is_empty hxswap),
        }, {
          rw hswap at hxswap,
          have hxsh: swap_head = x, {
            unfold swap_elems at hswap,
            symmetry,
            rw [take_zero, empty_concat, get_index] at hswap,
            from cons_injective_1 hswap,
          },
          rw hxsh at hxswap, clear hxsh,
          have := len_of_refl hswap,
          rw len_swap at this,
          rw this,
          simp,
          apply h_ih,
          from perm_head_cancel hxswap,
        },
      },
    },
  },
end

theorem is_perm_sorted_eq:
is_perm lst1 lst2 → is_sorted lst1 → is_sorted lst2
  → lst1 = lst2 :=
begin
  assume hp12 hs1 hs2,
  have hl12 := perm_len hp12,
  induction hl: len lst1 with n hn generalizing lst1 lst2, {
    rw [zz, ←empty_iff_len_zero] at hl,
    rw hl,
    rw hl at hp12,
    symmetry,
    from empty_perm_is_empty (perm_symm hp12),
  }, {
    cases lst1 with x xs, {
      contradiction,
    }, {
      cases lst2 with y ys, {
        contradiction,
      }, {
        have hxy: x = y, {
          -- note this is not use of classical reasoning, since
          -- we know = is decidable
          by_contradiction hxy',
          -- note sure if it would be worth it to use wlog or not
          -- is_sorted (y :: xs) seems like a pain to prove
          by_cases hxy'': x ≤ y, {
            have hxly := lt_iff_le_and_neq.mpr ⟨hxy'', hxy'⟩,
            have h :=
              hs2 0 (index x (y :: ys)
                begin
                  rw ←hp12 x,
                  rw count_head_eq,
                  from succ_ne_zero,
                end)
                (index_valid _)
                begin
                  unfold index,
                  rw dif_neg hxy',
                  from zero_lt_succ,
                end,
            rw get_zero_cons at h,
            rw get_index at h,
            contradiction,
          }, {
            have h :=
              hs1 0 (index y (x :: xs)
                begin
                  rw hp12 y,
                  rw count_head_eq,
                  from succ_ne_zero,
                end)
                (index_valid _)
                begin
                  unfold index,
                  have : ¬y = x, {
                    assume h,
                    from hxy' h.symm,
                  },
                  rw dif_neg this,
                  from zero_lt_succ,
                end,
            rw get_zero_cons at h,
            rw get_index at h,
            contradiction,
          },
        },
        rw hxy,
        simp,
        apply hn _ (tail_sorted hs1) (tail_sorted hs2), {
          simp at hl12,
          assumption,
        }, {
          simp at hl,
          assumption,
        }, {
          rw hxy at hp12,
          from perm_head_cancel hp12,
        },
      }
    }
  }
end

end hidden
