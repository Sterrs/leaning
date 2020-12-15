import .mylist
import .sorting

namespace hidden
namespace mylist

open mynat

universes u v
variables {T: Sort v} {T2: Sort u}
variables {T3: Type u} {T4: Type v}
variables {m n k: mynat}
variables {lst lst1 lst2: mylist T}
variables {lst' lst1' lst2': mylist T2}

-- classic map function
def map (f: T → T2): mylist T → mylist T2
| []        := []
| (x :: xs) := f x :: map xs

-- aka foldl
-- this form looks yuckier but I think it's nicer to prove things with
def reduce (f: T → T → T): Π lst: mylist T, lst ≠ [] → T
| [] h             := absurd rfl h
| (x :: []) h      := x
| (x :: y :: xs) h := f x (reduce (y :: xs) cons_not_empty)

-- reduce with a "default" value for empty lists
def reduce_d (f: T → T → T) (default: T): mylist T → T
| [] := default
| (x :: xs) := f x (reduce_d xs)

def for_all (p: T → Prop) (lst: mylist T): Prop :=
reduce_d and true (map p lst)

def for_some (p: T → Prop) (lst: mylist T): Prop :=
reduce_d or false (map p lst)

def contains (x: T3) (lst: mylist T3): Prop :=
for_some (λ y, x = y) lst

instance: has_mem T3 (mylist T3) := ⟨contains⟩

def filter (p: T → Prop)
[hpdec: ∀ t: T, decidable (p t)]: mylist T → mylist T
| [] := []
| (x :: xs) := if p x then x :: filter xs else filter xs

-- make n zeroes
def zeroes: mynat → mylist mynat
| 0        := []
| (succ n) := 0 :: zeroes n

-- list 0, 1, 2, ..., n - 1
def list_zero_to: mynat → mylist mynat
| 0        := []
| (succ n) := 0 :: map succ (list_zero_to n)

theorem for_all_iff_forall (p: T3 → Prop) (lst: mylist T3):
for_all p lst ↔ ∀ x: T3, contains x lst → p x :=
begin
  split, {
    assume hfa,
    induction lst with y ys ih_ys, {
      intro x,
      assume h,
      exfalso, from h,
    }, {
      intro x,
      assume h,
      cases h with h h, {
        rw h,
        from hfa.left,
      }, {
        apply ih_ys, {
          from hfa.right,
        }, {
          from h,
        },
      },
    },
  }, {
    assume hfa,
    induction lst with y ys ih_ys, {
      trivial,
    }, {
      split, {
        apply hfa,
        left,
        from rfl,
      }, {
        apply ih_ys,
        intro x,
        assume h,
        apply hfa,
        right,
        from h,
      },
    },
  },
end

theorem for_some_iff_exists (p: T3 → Prop) (lst: mylist T3):
for_some p lst ↔ ∃ x: T3, contains x lst ∧ p x :=
begin
  split, {
    assume hfs,
    induction lst with y ys ih_ys, {
      exfalso, from hfs,
    }, {
      cases hfs with hfs hfs, {
        existsi y,
        split, {
          left,
          from rfl,
        }, {
          assumption,
        },
      }, {
        cases ih_ys hfs with x hx,
        existsi x,
        split, {
          right,
          from hx.left,
        }, {
          from hx.right,
        },
      },
    },
  }, {
    assume hfs,
    induction lst with y ys ih_ys, {
      cases hfs with x hx,
      exfalso, from hx.left,
    }, {
      cases hfs with x hx,
      cases hx with hx hp,
      cases hx with hx hx, {
        left,
        rw ←hx,
        assumption,
      }, {
        right,
        apply ih_ys,
        existsi x,
        split; assumption,
      },
    },
  },
end

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

theorem contains_map (f: T3 → T4) (x: T3) (lst: mylist T3):
contains x lst → contains (f x) (map f lst) :=
begin
  assume hxl,
  induction lst with y ys ih_ys, {
    exfalso, from hxl,
  }, {
    cases hxl with hxl hxl, {
      rw hxl,
      left,
      from rfl,
    }, {
      right,
      apply ih_ys,
      assumption,
    },
  },
end

-- should probably be shortened or at least split up
theorem contains_filter (x: T3) (lst: mylist T3)
(p: T3 → Prop)
[hpdec: ∀ t: T3, decidable (p t)]:
contains x (filter p lst) ↔ contains x lst ∧ p x :=
begin
  split; assume hx, {
    split, {
      induction lst with y ys ih_ys, {
        exfalso, from hx,
      }, {
        by_cases hpy: p y, {
          unfold filter at hx,
          rw if_pos hpy at hx,
          cases hx with hx hx, {
            rw hx,
            left,
            from rfl,
          }, {
            right,
            apply ih_ys,
            assumption,
          },
        }, {
          unfold filter at hx,
          rw if_neg hpy at hx,
          right,
          apply ih_ys,
          assumption,
        },
      },
    }, {
      induction lst with y ys ih_ys, {
        exfalso, from hx,
      }, {
        by_cases hpy: p y, {
          unfold filter at hx,
          rw if_pos hpy at hx,
          cases hx with hx hx, {
            rw hx,
            assumption,
          }, {
            apply ih_ys,
            assumption,
          },
        }, {
          unfold filter at hx,
          rw if_neg hpy at hx,
          apply ih_ys,
          assumption,
        },
      },
    },
  }, {
    induction lst with y ys ih_ys, {
      exfalso,
      from hx.left,
    }, {
      by_cases hpy: p y, {
        unfold filter,
        rw if_pos hpy,
        cases hx.left with hxys hxys, {
          rw hxys,
          left,
          from rfl,
        }, {
          right,
          apply ih_ys,
          split, {
            assumption,
          }, {
            from hx.right,
          },
        },
      }, {
        unfold filter,
        rw if_neg hpy,
        apply ih_ys,
        split, {
          cases hx.left with hxys hxys, {
            rw ←hxys at hpy,
            exfalso,
            from hpy hx.right,
          }, {
            assumption,
          },
        }, {
          from hx.right,
        },
      },
    },
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

theorem map_concat (f: T → T2):
map f (lst1 ++ lst2) = map f lst1 ++ map f lst2 :=
begin
  induction lst1 with x xs ih_xs, {
    refl,
  }, {
    rw cons_concat,
    unfold map,
    rw ih_xs,
    refl,
  },
end


-- in anticipation of defining products of finite multisets

private lemma concat_nempty_left
{lst1 lst2: mylist T}
(h1: lst1 ≠ []):
lst1 ++ lst2 ≠ [] :=
begin
  rw nonempty_iff_len_nonzero at *,
  rw nzero_iff_zero_lt at *,
  rw len_concat_add,
  from lt_add_rhs h1,
end

private lemma concat_nempty_right
{lst1 lst2: mylist T}
(h2: lst2 ≠ []):
lst1 ++ lst2 ≠ [] :=
begin
  rw nonempty_iff_len_nonzero at *,
  rw nzero_iff_zero_lt at *,
  rw len_concat_add,
  rw add_comm,
  from lt_add_rhs h2,
end

theorem reduce_assoc_concat
(f: mynat → mynat → mynat)
(hassoc: is_associative _ f)
(lst1 lst2: mylist mynat)
(h1ne: lst1 ≠ []) (h2ne: lst2 ≠ []):
reduce f (lst1 ++ lst2) (concat_nempty_left h1ne) = f (reduce f lst1 h1ne) (reduce f lst2 h2ne) :=
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
      conv {
        to_lhs,
        congr, skip,
        rw cons_concat,
        rw cons_concat,
      },
      unfold reduce,
      have := hxs cons_not_empty,
      conv at this {
        to_lhs,
        congr, skip,
        rw cons_concat,
      },
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
reduce f (lst1 ++ lst2) (concat_nempty_left h1ne) = reduce f (lst2 ++ lst1) (concat_nempty_right h1ne) :=
begin
  cases lst1 with x xs, {
    contradiction,
  }, {
    cases lst2 with y ys, {
      simp,
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
reduce f (lst1 ++ lst2 ++ lst3) (concat_nempty_left (concat_nempty_left h1ne)) = reduce f (lst2 ++ lst1 ++ lst3) (concat_nempty_left (concat_nempty_right h1ne)) :=
begin
  cases lst3 with z zs, {
    conv {
      congr,
      congr, skip,
      rw concat_empty,
      skip, congr, skip,
      rw concat_empty,
    },
    apply reduce_comm_assoc_concat_comm _ hcomm hassoc,
    from h1ne,
  }, {
    rw reduce_assoc_concat f hassoc (lst1 ++ lst2) (z :: zs) _ cons_not_empty,
    rw reduce_assoc_concat f hassoc (lst2 ++ lst1) (z :: zs) _ cons_not_empty,
    rw reduce_comm_assoc_concat_comm f hcomm hassoc lst1 lst2 h1ne,
  },
end

private lemma reduce_comm_assoc_concat_interchange
(f: mynat → mynat → mynat)
(hcomm: is_commutative _ f)
(hassoc: is_associative _ f)
(a b c d e: mylist mynat)
(hb: b ≠ []) (hd: d ≠ []):
reduce f (a ++ b ++ c ++ d ++ e) (concat_nempty_left (concat_nempty_right hd)) = reduce f (a ++ d ++ c ++ b ++ e) (concat_nempty_left (concat_nempty_right hb)) :=
begin
  -- tragically we aren't allowed to clear these hypotheses
  have h1: (a ++ b ++ c ++ d ++ e) = (a ++ b) ++ (c ++ d) ++ e, {
    -- also known as a_refl
    repeat {rw ←concat_assoc},
  },
  conv {congr, congr, skip, rw h1},
  rw reduce_comm_assoc_concat_transpose f hcomm hassoc,
  have h2: (c ++ d ++ (a ++ b) ++ e) = (c ++ d ++ a) ++ (b ++ e), {
    repeat {rw ←concat_assoc},
  },
  conv {congr, congr, skip, rw h2},
  rw reduce_comm_assoc_concat_comm f hcomm hassoc,
  have h3: (b ++ e ++ (c ++ d ++ a)) = (b ++ e ++ c) ++ d ++ a, {
    repeat {rw ←concat_assoc},
  },
  conv {congr, congr, skip, rw h3},
  rw reduce_comm_assoc_concat_transpose f hcomm hassoc,
  have h4: (d ++ (b ++ e ++ c) ++ a) = (d ++ b ++ e ++ c) ++ a, {
    repeat {rw ←concat_assoc},
  },
  conv {congr, congr, skip, rw h4},
  rw reduce_comm_assoc_concat_comm f hcomm hassoc,
  have h5: (a ++ (d ++ b ++ e ++ c)) = (a ++ d) ++ b ++ (e ++ c), {
    repeat {rw ←concat_assoc},
  },
  conv {congr, congr, skip, rw h5},
  rw reduce_comm_assoc_concat_transpose f hcomm hassoc,
  have h6: (b ++ (a ++ d) ++ (e ++ c)) = (b ++ a ++ d ++ e) ++ c, {
    repeat {rw ←concat_assoc},
  },
  conv {congr, congr, skip, rw h6},
  rw reduce_comm_assoc_concat_comm f hcomm hassoc,
  have h7: (c ++ (b ++ a ++ d ++ e)) = (c ++ b) ++ (a ++ d) ++ e, {
    repeat {rw ←concat_assoc},
  },
  conv {congr, congr, skip, rw h7},
  rw reduce_comm_assoc_concat_transpose f hcomm hassoc,
  conv {congr, congr, skip},
  have h8: a ++ d ++ (c ++ b) ++ e = a ++ d ++ c ++ b ++ e, {
    repeat {rw ←concat_assoc},
  },
  conv {congr, congr, skip, rw h8},
  -- these are all concatenations involving a non-empty list
  from concat_nempty_right hb,
  from concat_nempty_left (concat_nempty_right hd),
  from concat_nempty_right hd,
  repeat {rw concat_assoc},
  from concat_nempty_left hd,
  from concat_nempty_left hb,
  from concat_nempty_right (concat_nempty_left hd),
  from concat_nempty_right hb,
end

theorem reduce_comm_assoc_swap
(f: mynat → mynat → mynat)
(hcomm: is_commutative _ f)
(hassoc: is_associative _ f)
(lst: mylist mynat)
(hmn: m < n)
(hnl: n < len lst):
reduce f lst (
  begin
    rw nonempty_iff_len_nonzero,
    rw nzero_iff_zero_lt,
    from le_lt_chain n zero_le hnl,
  end
) = reduce f (swap_elems m n lst hmn hnl) (
  begin
    rw nonempty_iff_len_nonzero,
    rw len_swap,
    rw nzero_iff_zero_lt,
    from le_lt_chain n zero_le hnl,
  end
) :=
begin
  unfold swap_elems,
  rw reduce_comm_assoc_concat_interchange f hcomm hassoc,
  congr,
  have := take_concat_drop (lt_impl_le (mynat.lt_trans hmn hnl)),
  conv in lst {rw ←this}, clear this,
  repeat {rw concat_assoc},
  congr,
  have := @cons_head_tail _ (drop m lst (lt_impl_le (mynat.lt_trans hmn hnl))) _,
  rw ←this, clear this,
  rw ←@get_head_drop _ lst m,
  rw singleton_concat_cons,
  congr,
  have := @drop_one_tail _ (drop m lst (lt_impl_le (mynat.lt_trans hmn hnl))) _,
  rw ←this, clear this,
  rw drop_drop,
  unfold slice,
  have := @take_concat_drop _ (drop m.succ lst _) (n - m.succ) _,
  conv {
    to_lhs,
    congr,
    rw add_one_succ,
  },
  conv {
    to_lhs,
    rw ←this,
  }, clear this,
  congr,
  rw drop_drop,
  have := sub_add_condition.mpr (lt_iff_succ_le.mp hmn),
  rw add_comm at this,
  conv {
    to_lhs,
    congr,
    rw this,
  },
  have := @cons_head_tail _ (drop n lst (lt_impl_le hnl)) _,
  rw ←this, clear this,
  rw ←@get_head_drop _ lst n,
  rw singleton_concat_cons,
  congr,
  rw ←@drop_one_tail _ (drop n lst _),
  rw drop_drop,
  refl,

  apply @le_cancel _ _ n,
  rw len_drop,
  rw add_comm,
  from lt_iff_succ_le.mp hnl,

  apply @le_cancel _ _ m,
  rw len_drop,
  rw add_comm,
  from lt_iff_succ_le.mp (lt_trans hmn hnl),

  from cons_not_empty,
  from cons_not_empty,
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
        have hidxy: count y (x :: xs) ≠ 0, {
          rw hperm y,
          unfold count,
          rw if_pos rfl,
          from succ_ne_zero,
        },
        by_cases hxy: x = y, {
          conv {congr, congr, skip, rw hxy},
          cases xs with x' xs, {
            cases ys with y' ys, {
              refl,
            }, {
              cases hl1l2,
            },
          },
          cases ys with y' ys, {
            cases hl1l2,
          }, {
            apply reduce_congr f y (x' :: xs) (y' :: ys) cons_not_empty cons_not_empty,
            apply hn,
            rw hxy at hperm,
            from perm_head_cancel hperm,
            from succ_inj hl,
          },
        }, {
          have h0lidxy: 0 < index y (x :: xs) hidxy, {
            assume h,
            have hidxy0 := le_zero_iff.mp h,
            have := get_index hidxy (index_valid _),
            conv at this {
              congr,
              congr,
              rw hidxy0,
            },
            dsimp at this,
            contradiction,
          },
          have hswapne: swap_elems 0 (index y (x :: xs) hidxy) (x :: xs) h0lidxy (index_valid _) ≠ mylist.empty, {
            rw nonempty_iff_len_nonzero,
            rw len_swap,
            from succ_ne_zero,
          },
          transitivity reduce f (swap_elems 0 (index y (x :: xs) hidxy) (x :: xs) h0lidxy (index_valid _)) hswapne, {
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
            cases ys with y' ys, {
              have: count y (x :: xs) = 0, {
                unfold count,
                rw if_neg (λ h, hxy (eq.symm h)),
                rw empty_iff_len_zero.mpr (succ_inj hl1l2),
                refl,
              },
              contradiction,
            }, {
              apply reduce_congr f y _ (y' :: ys) _ cons_not_empty,
              apply hn,
              apply @perm_head_cancel y,
              apply @perm_trans _ (x :: xs) _,
              have := @swap_perm 0 (index y (x :: xs) hidxy) (x :: xs) _ _,
              unfold swap_elems at this,
              dsimp at this,
              rw get_index at this,
              from perm_symm this,
              assumption,

              suffices: len (swap_elems 0 (index y (x :: xs) hidxy) (x :: xs) _ _) = n.succ,
              unfold swap_elems at this,
              dsimp at this,
              repeat {rw len_concat_add at this},
              simp at this,
              simp,
              assumption,

              have := @swap_perm 0 (index y (x :: xs) hidxy) (x :: xs) _ _,
              rw ←hl,
              apply perm_len,
              apply perm_symm,
              assumption,

              rw nonempty_iff_len_nonzero,
              rw nzero_iff_zero_lt,
              rw len_concat_add,
              rw len_concat_add,
              unfold len,
              repeat {rw add_succ <|> rw succ_add},
              from zero_lt_succ,
            }
          },
        },
      },
    },
  },
end

end mylist
end hidden
