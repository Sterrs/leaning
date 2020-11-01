import .mylist
import .sorting

namespace hidden

open mynat

universe u
variables {T T2: Sort u}
variables {m n k: mynat}
variables {lst lst1 lst2: mylist T}
variables {lst' lst1' lst2': mylist T2}

-- classic map function
def map (f: T → T2): mylist T → mylist T2
| []        := []
| (x :: xs) := f x :: map xs

-- aka foldl
-- it seemed to be quite disgusting to have a special identity value to return
-- for empty lists
def reduce (f: T → T → T): Π lst: mylist T, lst ≠ [] → T
| [] h             := absurd rfl h
| (x :: []) h      := x
| (x :: y :: xs) h := f x (reduce (y :: xs) cons_not_empty)

-- make n zeroes
def zeroes: mynat → mylist mynat
| 0        := []
| (succ n) := 0 :: zeroes n

-- list 0, 1, 2, ..., n - 1
def list_zero_to: mynat → mylist mynat
| 0        := []
| (succ n) := 0 :: map succ (list_zero_to n)

theorem len_zeroes: len (zeroes m) = m :=
begin
  induction m with m hm, {
    refl,
  }, {
    unfold zeroes,
    unfold len,
    rw hm,
  },
end

theorem get_a_zero
(hml: m < len (zeroes n)):
get m (zeroes n) hml = (0: mynat) :=
begin
  induction n with n hn generalizing m, {
    exfalso,
    from lt_nzero hml,
  }, {
    unfold zeroes,
    cases m, {
      refl,
    }, {
      unfold get,
      apply hn,
    },
  },
end

theorem len_map
(f: T → T2):
len (map f lst) = len lst :=
begin
  induction lst with head tail h_ih, {
    refl,
  }, {
    unfold map,
    unfold len,
    rw h_ih,
  },
end

theorem len_list_zero_to: len (list_zero_to m) = m :=
begin
  induction m with m hm, {
    refl,
  }, {
    unfold list_zero_to,
    unfold len,
    rw len_map,
    rw hm,
  },
end

theorem get_map'
(f: T → T2)
(hml: m < len lst)
(hml': m < len (map f lst)):
get m (map f lst) hml' = f (get m lst hml) :=
begin
  induction lst with head tail h_ih generalizing m, {
    exfalso,
    from lt_nzero hml,
  }, {
    cases m, {
      refl,
    }, {
      unfold map,
      unfold get,
      apply h_ih,
    },
  },
end

-- more useful version for simplifying rewrites
theorem get_map
(f: T → T2)
(hml: m < len (map f lst)):
get m (map f lst) hml
  = f (get m lst begin rw len_map at hml, assumption, end)
:= get_map' _ _ _

theorem get_zero_to
(hnl: n < len (list_zero_to m)):
get n (list_zero_to m) hnl = n :=
begin
  induction m with m hm generalizing n, {
    exfalso,
    from lt_nzero hnl,
  }, {
    unfold list_zero_to,
    cases n, {
      refl,
    }, {
      unfold get,
      rw get_map,
      rw hm,
    },
  },
end

-- in anticipation of defining products of finite multisets

theorem reduce_assoc_concat
(f: mynat → mynat → mynat)
(hassoc: is_associative _ f)
(lst1 lst2: mylist mynat)
(h1ne: lst1 ≠ []) (h2ne: lst2 ≠ []):
reduce f (lst1 ++ lst2) sorry = f (reduce f lst1 h1ne) (reduce f lst2 h2ne) :=
begin
  induction lst1 with x xs hxs, {
    contradiction,
  }, {
    cases xs with x' xs, {
      dsimp,
      unfold reduce,
      cases lst2 with y ys, {
        contradiction,
      }, {
        refl,
      },
    }, {
      unfold reduce,
      rw cons_concat,
      rw cons_concat,
      unfold reduce,
      have := hxs cons_not_empty,
      rw cons_concat at this,
      rw this,
      symmetry,
      apply hassoc.assoc,
    },
  },
end

theorem reduce_comm_assoc_concat_comm
(f: mynat → mynat → mynat)
(hcomm: is_commutative _ f)
(hassoc: is_associative _ f)
(lst1 lst2: mylist mynat)
(h1ne: lst1 ≠ []):
reduce f (lst1 ++ lst2) sorry = reduce f (lst2 ++ lst1) sorry :=
begin
  cases lst1 with x xs, {
    contradiction,
  }, {
    cases lst2 with y ys, {
      rw concat_empty,
      refl,
    }, {
      rw reduce_assoc_concat f hassoc (x :: xs) (y :: ys) cons_not_empty cons_not_empty,
      rw reduce_assoc_concat f hassoc (y :: ys) (x :: xs) cons_not_empty cons_not_empty,
      apply hcomm.comm,
    },
  },
end

theorem reduce_comm_assoc_concat_transpose
(f: mynat → mynat → mynat)
(hcomm: is_commutative _ f)
(hassoc: is_associative _ f)
(lst1 lst2 lst3: mylist mynat)
(h1ne: lst1 ≠ []):
reduce f (lst1 ++ lst2 ++ lst3) sorry = reduce f (lst2 ++ lst1 ++ lst3) sorry :=
begin
  cases lst3 with z zs, {
    repeat {rw concat_empty},
    apply reduce_comm_assoc_concat_comm _ hcomm hassoc,
    from h1ne,
  }, {
    rw reduce_assoc_concat f hassoc (lst1 ++ lst2) (z :: zs) sorry cons_not_empty,
    rw reduce_assoc_concat f hassoc (lst2 ++ lst1) (z :: zs) sorry cons_not_empty,
    rw reduce_comm_assoc_concat_comm f hcomm hassoc lst1 lst2 h1ne,
  },
end

private lemma reduce_comm_assoc_concat_interchange
(f: mynat → mynat → mynat)
(hcomm: is_commutative _ f)
(hassoc: is_associative _ f)
(a b c d e: mylist mynat)
(hb: b ≠ []) (hd: d ≠ []):
reduce f (a ++ b ++ c ++ d ++ e) sorry = reduce f (a ++ d ++ c ++ b ++ e) sorry :=
begin
  have: (a ++ b ++ c ++ d ++ e) = (a ++ b) ++ (c ++ d) ++ e, {
    -- also known as a_refl
    repeat {rw ←concat_assoc},
  },
  rw this, clear this,
  rw reduce_comm_assoc_concat_transpose f hcomm hassoc,
  have: (c ++ d ++ (a ++ b) ++ e) = (c ++ d ++ a) ++ (b ++ e), {
    repeat {rw ←concat_assoc},
  },
  rw this, clear this,
  rw reduce_comm_assoc_concat_comm f hcomm hassoc,
  have: (b ++ e ++ (c ++ d ++ a)) = (b ++ e ++ c) ++ d ++ a, {
    repeat {rw ←concat_assoc},
  },
  rw this, clear this,
  rw reduce_comm_assoc_concat_transpose f hcomm hassoc,
  have: (d ++ (b ++ e ++ c) ++ a) = (d ++ b ++ e ++ c) ++ a, {
    repeat {rw ←concat_assoc},
  },
  rw this, clear this,
  rw reduce_comm_assoc_concat_comm f hcomm hassoc,
  have: (a ++ (d ++ b ++ e ++ c)) = (a ++ d) ++ b ++ (e ++ c), {
    repeat {rw ←concat_assoc},
  },
  rw this, clear this,
  rw reduce_comm_assoc_concat_transpose f hcomm hassoc,
  have: (b ++ (a ++ d) ++ (e ++ c)) = (b ++ a ++ d ++ e) ++ c, {
    repeat {rw ←concat_assoc},
  },
  rw this, clear this,
  rw reduce_comm_assoc_concat_comm f hcomm hassoc,
  have: (c ++ (b ++ a ++ d ++ e)) = (c ++ b) ++ (a ++ d) ++ e, {
    repeat {rw ←concat_assoc},
  },
  rw this, clear this,
  rw reduce_comm_assoc_concat_transpose f hcomm hassoc,
  repeat {rw ←concat_assoc},
  -- these are all concatenations involving a non-empty list
  repeat {sorry},
end

theorem reduce_comm_assoc_swap
(f: mynat → mynat → mynat)
(hcomm: is_commutative _ f)
(hassoc: is_associative _ f)
(lst: mylist mynat)
(hmn: m < n)
(hnl: n < len lst):
reduce f lst sorry = reduce f (swap_elems m n lst hmn hnl) sorry :=
begin
  unfold swap_elems,
  rw reduce_comm_assoc_concat_interchange f hcomm hassoc,
  congr,
  have := take_concat_drop (lt_impl_le (mynat.lt_trans hmn hnl)) (lt_impl_le (mynat.lt_trans hmn hnl)),
  conv in lst {rw ←this}, clear this,
  repeat {rw concat_assoc},
  congr,
  have := @cons_head_tail _ (drop m lst (lt_impl_le (mynat.lt_trans hmn hnl))) sorry,
  rw ←this, clear this,
  rw ←@get_head_drop _ lst m (lt_impl_le (mynat.lt_trans hmn hnl)) (mynat.lt_trans hmn hnl),
  rw singleton_concat_cons,
  congr,
  have := @drop_one_tail _ (drop m lst (lt_impl_le (mynat.lt_trans hmn hnl))) sorry,
  rw ←this, clear this,
  rw drop_drop sorry sorry sorry,
  unfold slice,
  have := @take_concat_drop _ (drop m.succ lst sorry) (n - m.succ) sorry sorry,
  conv {
    to_lhs,
    rw add_one_succ,
    rw ←this,
  }, clear this,
  congr,
  rw drop_drop sorry sorry sorry,
  have := sub_add_condition.mpr (lt_iff_succ_le.mp hmn),
  rw add_comm at this,
  rw this, clear this,
  have := @cons_head_tail _ (drop n lst (lt_impl_le hnl)) sorry,
  rw ←this, clear this,
  rw ←@get_head_drop _ lst n sorry sorry sorry,
  rw singleton_concat_cons,
  congr,
  rw ←@drop_one_tail _ (drop n lst sorry) sorry sorry,
  rw drop_drop sorry sorry sorry,
  refl,
  sorry, sorry,
end

-- takes some of the casework out
theorem reduce_congr
(f: mynat → mynat → mynat)
(x: mynat) (xs ys: mylist mynat)
(hxs: xs ≠ []) (hys: ys ≠ []):
reduce f xs hxs = reduce f ys hys
→ reduce f (x :: xs) cons_not_empty = reduce f (x :: ys) cons_not_empty :=
begin
  assume h,
  cases xs with x' xs, {
    contradiction,
  }, {
    cases ys with y' ys, {
      contradiction,
    }, {
      unfold reduce,
      congr,
      assumption,
    },
  },
end

-- TODO: for general types with decidable_eq
theorem reduce_comm_assoc_perm
(f: mynat → mynat → mynat)
(hcomm: is_commutative _ f)
(hassoc: is_associative _ f)
(lst1 lst2: mylist mynat)
(h1ne: lst1 ≠ []) (h2ne: lst2 ≠ [])
(hperm: is_perm lst1 lst2):
reduce f lst1 h1ne = reduce f lst2 h2ne :=
begin
  induction hl: len lst1 with n hn generalizing lst1 lst2, {
    have := empty_iff_len_zero.mpr hl,
    contradiction,
  }, {
    have hl1l2 := perm_len hperm,
    cases lst1 with x xs, {
      contradiction,
    }, {
      cases lst2 with y ys, {
        contradiction,
      }, {
        transitivity reduce f (swap_elems 0 (index y (x :: xs) sorry) (x :: xs) sorry sorry) sorry, {
          apply reduce_comm_assoc_swap,
          from hcomm,
          from hassoc,
        }, {
          unfold swap_elems,
          dsimp,
          conv {
            to_lhs,
            congr, skip, congr,
            rw get_index,
          },
          apply reduce_congr f y _ ys sorry sorry,
          apply hn,
          apply @perm_head_cancel y,
          apply @perm_trans _ (x :: xs) _,
          have := @swap_perm 0 (index y (x :: xs) sorry) (x :: xs) sorry sorry,
          unfold swap_elems at this,
          dsimp at this,
          rw get_index at this,
          from perm_symm this,
          assumption,

          suffices: len (swap_elems 0 (index y (x :: xs) sorry) (x :: xs) sorry sorry) = n.succ,
          unfold swap_elems at this,
          dsimp at this,
          repeat {rw len_concat_add at this},
          simp at this,
          simp,
          assumption,

          have := @swap_perm 0 (index y (x :: xs) sorry) (x :: xs) sorry sorry,
          rw ←hl,
          apply perm_len,
          apply perm_symm,
          assumption,
        },
      },
    },
  },
end

end hidden
