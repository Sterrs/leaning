-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import ..mynat.basic
import ..mynat.lt
import ..mynat.induction

namespace hidden

universe u

-- list of elements of type T
inductive mylist (T: Sort u)
-- allow empty to infer its type. It doesn't seem to work very often
| empty {}: mylist
| cons (head: T) (tail: mylist): mylist

open mylist
open mynat

namespace mylist

variable {T: Sort u}
-- Haskell-like convention, use x::xs to pattern match head/tail
variables {x y z: T}
variables {xs ys zs lst lst1 lst2 lst3: mylist T}
variables {m n: mynat}

-- I'm really just sort of making this up as I go along
-- It would be nice to have notation like [1, 2, 3]
notation h :: t := cons h t
def singleton (x: T) := x :: (empty: mylist T)

theorem cons_injective_1: x :: xs = y :: ys → x = y :=
λ h, (cons.inj h).left

theorem cons_injective_2: x :: xs = y :: ys → xs = ys :=
λ h, (cons.inj h).right

-- we don't define append explicitly, since lists are define by
-- recursion on the tail. Also note that concat is defined by
-- recursion on the first argument, so you should generally induct on
-- the first argument.
def concat: mylist T → mylist T → mylist T
| empty        lst := lst
| (x :: xs) lst := x :: (concat xs lst)

notation lst1 ++ lst2 := concat lst1 lst2

@[simp] theorem empty_concat: (empty: mylist T) ++ lst = lst := rfl
@[simp]
theorem cons_concat: (x :: xs) ++ lst = x :: (xs ++ lst) := rfl

@[simp]
theorem concat_empty: lst ++ (empty: mylist T) = lst :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    simp,
  }, {
    simp [lst_ih],
  },
end

@[simp]
theorem singleton_concat_cons: singleton x ++ lst = x :: lst := rfl

@[simp]
theorem cons_not_empty: x :: xs ≠ empty :=
begin
  assume h,
  cases h,
end

@[simp]
theorem concat_assoc: (lst1 ++ lst2) ++ lst3 = lst1 ++ (lst2 ++ lst3) :=
begin
  induction lst1 with lst1_head lst1_tail lst1_ih, {
    simp,
  }, {
   simp [lst1_ih],
  },
end

instance concat_is_assoc (T: Type u): is_associative (mylist T) concat :=
⟨λ a b c, concat_assoc⟩

def len: mylist T → mynat
| empty        := 0
| (_ :: xs) := succ (len xs)

@[simp]
theorem empty_len: len (empty: mylist T) = 0 := rfl

@[simp]
theorem len_cons_succ: len (x :: xs) = succ (len xs) := rfl

@[simp]
theorem len_singleton: len (singleton x) = 1 := len_cons_succ

theorem len_of_refl: lst1 = lst2 → len lst1 = len lst2 :=
begin
  assume h,
  rw h,
end

@[simp]
theorem len_concat_add: len (lst1 ++ lst2) = len lst1 + len lst2 :=
begin
  induction lst1 with lst1_head lst1_tail lst1_ih, {
    simp,
  }, {
    simp [lst1_ih],
  },
end

def rev: mylist T → mylist T
| empty        := empty
| (x :: xs) := (rev xs) ++ singleton x

@[simp] theorem rev_empty: rev (empty: mylist T) = empty := rfl
@[simp] theorem rev_cons: rev (x :: xs) = (rev xs) ++ singleton x := rfl
@[simp] theorem rev_singleton: rev (singleton x) = singleton x := rfl

@[simp]
theorem rev_append: rev (lst ++ singleton x) = x :: rev lst :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    refl,
  }, {
    rw [cons_concat, rev_cons, lst_ih],
    refl,
  },
end

theorem rev_concat: rev (lst1 ++ lst2) = rev lst2 ++ rev lst1 :=
begin
  induction lst1 with lst1_head lst1_tail lst1_ih, {
    rw rev_empty,
    rw concat_empty,
    refl,
  }, {
    rw [cons_concat, rev_cons, lst1_ih, rev_cons, concat_assoc],
  },
end

@[simp]
theorem rev_rev: rev (rev lst) = lst :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    simp,
  }, {
    simp [lst_ih, rev_concat],
  },
end

@[simp]
theorem rev_len: len (rev lst) = len lst :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    simp,
  }, {
    simp [lst_ih],
  },
end

theorem empty_iff_len_zero: lst = empty ↔ len lst = 0 :=
begin
  split, {
    assume h,
    rw h,
    refl,
  }, {
    assume h,
    cases lst, {
      refl,
    }, {
      exfalso,
      from succ_ne_zero h,
    },
  },
end

theorem nonempty_iff_len_nonzero: lst ≠ empty ↔ len lst ≠ 0 :=
iff_to_contrapositive empty_iff_len_zero

theorem rev_not_empty: lst ≠ empty → rev lst ≠ empty :=
begin
  repeat {rw nonempty_iff_len_nonzero},
  rw rev_len,
  assume h, from h,
end

-- These are some "maybe" operations, which are undefined on empty lists
-- (or sometimes lists of a certain length), so they take as argument
-- a proof that the input list is of the correct form,
-- which is a dependent type thing. Maybe they're supposed to be Πs

-- first element
def head: Π lst: mylist T, lst ≠ empty → T
| empty       h := absurd rfl h
| (x :: _) _ := x

@[simp] theorem first_cons (h: x :: xs ≠ empty): head (x :: xs) h = x := rfl

-- everything except first element
def tail: Π lst: mylist T, lst ≠ empty → mylist T
| empty        h := absurd rfl h
| (_ :: xs) _ := xs

@[simp] theorem tail_cons (h: x :: xs ≠ empty): tail (x :: xs) h = xs := rfl

-- everything except last element
def init: Π lst: mylist T, lst ≠ empty → mylist T
| empty             h := absurd rfl h
| (x :: empty)      _ := empty
| (x :: y :: xs) _ := x :: init (y :: xs) cons_not_empty

@[simp]
theorem init_singleton (h: singleton x ≠ empty):
init (singleton x) h = empty := rfl

@[simp]
theorem init_ccons (h: x :: y :: xs ≠ empty):
init (x :: y :: xs) h = x :: init (y :: xs) cons_not_empty := rfl

-- last element
def last: Π lst: mylist T, lst ≠ empty → T
| empty             h := absurd rfl h
| (x :: empty)      _ := x
| (x :: y :: xs) h := last (y :: xs) cons_not_empty

@[simp]
theorem last_singleton (h: singleton x ≠ empty):
last (singleton x) h = x := rfl

@[simp]
theorem last_ccons (h: x :: y :: xs ≠ empty):
last (x :: y :: xs) h = last (y :: xs) cons_not_empty := rfl

private theorem len_cons_succ_cancel1 (h: succ n ≤ len (x :: xs)): n ≤ len xs :=
begin
  simp at h,
  from le_succ_cancel h,
end

private theorem absurd_succ_le_zero: ¬succ n ≤ 0 :=
begin
  assume h,
  simp [le_iff_lt_succ] at h,
  exfalso, from lt_nzero (lt_succ_cancel h),
end

-- the first n elements
def take: Π n: mynat, Π lst: mylist T, n ≤ len lst → mylist T
| 0        _         _ := empty
| (succ n) empty        h := absurd h absurd_succ_le_zero
| (succ n) (x :: xs) h := x :: take n xs (len_cons_succ_cancel1 h)

@[simp] theorem take_zero (h: 0 ≤ len lst): take 0 lst h = empty := rfl

@[simp]
theorem take_succ_cons
(h: succ n ≤ len (x :: xs)):
take (succ n) (x :: xs) h
  = x :: take n xs (len_cons_succ_cancel1 h) := rfl

-- everything except the first n elements
def drop: Π n: mynat, Π lst: mylist T, n ≤ len lst → mylist T
| 0        lst       _ := lst
| (succ n) empty        h := absurd h absurd_succ_le_zero
| (succ n) (_ :: xs) h := drop n xs (len_cons_succ_cancel1 h)

@[simp] theorem drop_zero (h: 0 ≤ len lst): drop 0 lst h = lst := rfl
@[simp]
theorem drop_succ_cons
(h: succ n ≤ len (x :: xs)):
drop (succ n) (x :: xs) h = drop n xs (len_cons_succ_cancel1 h) := rfl

private theorem len_cons_succ_cancel2 (h: succ n < len (x :: xs)):
n < len xs :=
begin
  simp at h,
  from lt_succ_cancel h,
end

-- the nth element
def get: Π n: mynat, Π lst: mylist T, n < len lst → T
| n        empty        h := absurd h lt_nzero
| 0        (x :: _)  _ := x
| (succ n) (x :: xs) h := get n xs (len_cons_succ_cancel2 h)

@[simp]
theorem get_zero_cons
(h: 0 < len (x :: xs)):
get 0 (x :: xs) h = x := rfl

@[simp]
theorem get_succ_cons
(h: succ n < len (x :: xs)):
get (succ n) (x :: xs) h = get n xs (len_cons_succ_cancel2 h) := rfl

-- TODO: state this without tactic mode
@[simp] theorem get_zero_head (h: 0 < len lst):
get 0 lst h = head lst
              begin
                assume h',
                simp [h', lt_nrefl] at h,
                assumption,
              end :=
begin
  cases lst, {
    refl,
  }, {
    simp,
  },
end

theorem cons_head_tail (h: lst ≠ empty): head lst h :: tail lst h = lst :=
begin
  cases lst, {
    contradiction,
  }, {
    simp,
  },
end

theorem len_tail (h: lst ≠ empty): len lst = succ (len (tail lst h)) :=
begin
  cases lst, {
    contradiction,
  }, {
    simp,
  },
end

-- I didn't really think this one through
theorem len_init (h: lst ≠ empty): len lst = succ (len (init lst h)) :=
begin
  induction lst, {
    contradiction,
  }, {
    cases lst_tail, {
      refl,
    }, {
      have := lst_ih cons_not_empty,
      dsimp [len] at this,
      dsimp [len],
      rw this,
    },
  },
end

theorem append_init_last (h: lst ≠ empty):
init lst h ++ (singleton (last lst h)) = lst :=
begin
  induction lst, {
    from absurd rfl h,
  }, {
    cases lst_tail, {
      refl,
    }, {
      rw init_ccons h,
      rw last_ccons h,
      simp,
      apply lst_ih,
    },
  },
end

private theorem succ_le_impl_le (h: succ n ≤ len lst): n ≤ len lst :=
(le_cancel_strong 1 h)

theorem len_take_succ
(hsnl: succ n ≤ len lst):
len (take (succ n) lst hsnl)
  = succ (len (take n lst (succ_le_impl_le hsnl))) :=
begin
  induction n with n_n n_ih generalizing lst, {
    simp,
    cases lst, {
      exfalso,
      simp at hsnl, -- clearly absurd. Is there a quicker way?
      cases hsnl with d hd,
      from mynat.no_confusion (add_integral hd.symm),
    }, {
      -- why on Earth is this SO DIFFICULT
      -- I don't understand why I can't go straight to the rw
      have h: (1: mynat) = succ 0 := rfl,
      conv {
        to_lhs,
        congr,
        congr,
        rw h,
      },
      rw take_succ_cons,
      simp,
    },
  }, {
    cases lst, {
      exfalso,
      cases hsnl with d hd,
      from mynat.no_confusion (add_integral hd.symm),
    }, {
      simp,
      rw len_cons_succ at hsnl,
      from n_ih (le_succ_cancel hsnl),
    },
  },
end

@[simp]
theorem len_take (hnl: n ≤ len lst):
len (take n lst hnl) = n :=
begin
  induction n, {
    refl,
  }, {
    -- really all the hard work happens in len_take_succ
    simp [len_take_succ],
    apply n_ih,
  },
end

theorem take_concat_drop (hnl: n ≤ len lst):
take n lst hnl ++ drop n lst hnl = lst :=
begin
  induction n generalizing lst, {
    refl,
  }, {
    cases lst, {
      simp at hnl,
      cases hnl with d hd,
      rw succ_add at hd,
      cases hd,
    }, {
      simp,
      apply n_ih,
    },
  },
end

theorem len_drop (hnl: n ≤ len lst):
len (drop n lst hnl) + n = len lst :=
begin
  conv {
    to_lhs, congr, skip,
    rw ←len_take hnl,
  },
  rw [add_comm, ←len_concat_add, take_concat_drop],
end

theorem get_head_drop
(hnl: n < len lst):
get n lst hnl = head (drop n lst (lt_impl_le hnl)) (
  begin
    rw nonempty_iff_len_nonzero,
    have := len_drop (lt_impl_le hnl),
    rw ←this at hnl,
    conv at hnl {
      to_lhs,
      rw ←add_zero n,
      rw add_comm,
    },
    have this2 := lt_cancel n hnl,
    assume h,
    rw h at this2,
    from lt_nrefl this2,
  end
) :=
begin
  induction n generalizing lst, {
    simp,
  }, {
    cases lst, {
      exfalso, from lt_nzero hnl,
    }, {
      simp,
      apply n_ih,
    },
  },
end

theorem concat_cancel_left: lst1 ++ lst2 = lst1 ++ lst3 → lst2 = lst3 :=
begin
  assume hl1l2l1l3,
  induction lst1, {
    simp at hl1l2l1l3,
    assumption,
  }, {
    simp at hl1l2l1l3,
    apply lst1_ih,
    assumption,
  },
end

theorem rev_injective: rev lst1 = rev lst2 → lst1 = lst2 :=
begin
  -- this is a bit silly. Is there a better way to apply
  -- something to both sides in Lean?
  assume hrl1rl2,
  suffices hrr: rev (rev lst1) = rev (rev lst2), {
    repeat {rw rev_rev at hrr},
    assumption,
  }, {
    rw hrl1rl2,
  },
end

theorem concat_cancel_right: lst2 ++ lst1 = lst3 ++ lst1 → lst2 = lst3 :=
begin
  assume hl1l2l1l3,
  apply rev_injective,
  apply @concat_cancel_left _ (rev lst1),
  rw [←rev_concat, hl1l2l1l3, rev_concat],
end

@[simp]
theorem take_all (h: len lst ≤ len lst): take (len lst) lst h = lst :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    refl,
  }, {
    simp,
    from lst_ih _,
  },
end

@[simp]
theorem drop_all (h: len lst ≤ len lst): drop (len lst) lst h = empty :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    refl,
  }, {
    simp,
    from lst_ih _,
  },
end

theorem take_idem
(hml: m ≤ len lst):
take m (take m lst hml) (
  begin
    rw len_take,
  end
) = take m lst hml :=
begin
  induction m with m hm generalizing lst, {
    refl,
  }, {
    cases lst, {
      exfalso,
      from lt_nzero (lt_iff_succ_le.mpr hml),
    }, {
      simp,
      apply hm,
    },
  },
end

theorem take_take
(hml: m ≤ len lst)
(hnl: n ≤ len (take m lst hml)):
take n (take m lst hml) hnl = take n lst (
  begin
    rw len_take at hnl,
    from le_trans hnl hml,
  end
) :=
begin
  induction n with n hn generalizing m lst, {
    refl,
  }, {
    cases lst, {
      exfalso,
      rw len_take at hnl,
      from lt_nzero (lt_iff_succ_le.mpr (le_trans hnl hml)),
    }, {
      cases m, {
        exfalso,
        simp at hnl,
        from lt_nzero (lt_iff_succ_le.mpr hnl),
      }, {
        simp,
        apply hn,
      },
    },
  },
end

theorem drop_drop
(hml: m ≤ len lst)
(hnl: n ≤ len (drop m lst hml)):
drop n (drop m lst hml) hnl = drop (m + n) lst (
  begin
    rw ←len_drop hml,
    rw add_comm m n,
    from le_comb hnl le_refl,
  end
) :=
begin
  induction m with m hm generalizing n lst, {
    simp,
  }, {
    cases lst, {
      exfalso,
      from succ_ne_zero (le_zero hml),
    }, {
      simp,
      apply hm,
    },
  },
end

theorem drop_one_tail
(h1l: 1 ≤ len lst):
drop 1 lst h1l = tail lst (
  begin
    rw nonempty_iff_len_nonzero,
    assume h,
    rw h at h1l,
    from succ_nle_zero h1l,
  end
) :=
begin
  cases lst, {
    refl,
  }, {
    refl,
  },
end

theorem take_init
(hnl: len xs ≤ len (xs ++ singleton x)):
take (len xs) (xs ++ singleton x) hnl = xs :=
begin
  induction xs, {
    refl,
  }, {
    simp,
    apply xs_ih,
  },
end

theorem take_ignore
(hnl: n ≤ len xs):
take n (xs ++ singleton x) (
  begin
    rw len_concat_add,
    from le_add_rhs hnl,
  end
  ) = take n xs hnl :=
begin
  suffices h:
      take n (take (len xs) (xs ++ singleton x) _) _ = take n xs hnl, {
    rw @take_take _ (xs ++ singleton x) (len xs) n _ _ at h,
    from h,
  }, {
    conv {
      to_lhs,
      congr, skip,
      rw take_init,
    },
  }, {
    simp,
    from @le_to_add _ 1,
  }, {
    simp,
    assumption,
  },
end

theorem rev_drop_take
(hmn: m + n = len lst):
drop m lst (
  begin
    rw ←hmn,
    from le_to_add,
  end
) = rev (take n (rev lst) (
  begin
    rw rev_len,
    rw ←hmn,
    rw add_comm,
    from le_to_add,
  end
)) :=
begin
  induction m with m hm generalizing lst, {
    simp at hmn,
    conv in n {rw hmn},
    conv in (len lst) {rw ←rev_len},
    rw take_all,
    conv in zero {rw zz},
    rw drop_zero,
    rw rev_rev,
  }, {
    cases lst, {
      exfalso,
      rw succ_add at hmn,
      from succ_ne_zero hmn,
    }, {
      rw drop_succ_cons,
      have hmlt: m + n = len lst_tail, {
        simp at hmn,
        assumption,
      },
      have := hm hmlt, {
        rw this,
        conv in (rev (lst_head :: lst_tail)) {rw rev_cons},
        rw take_ignore,
      },
    },
  },
end

-- for some reason this has to be a Type ???
-- otherwise has_mem complains
variable {T': Type u}
variables {x' y' z': T'}
variables {xs' ys' zs': mylist T'}

-- the well-founded relation "is one strictly shorter than the other"
def shorter (lst1 lst2: mylist T) := len lst1 < len lst2

private theorem shorter_lt:
shorter lst1 lst2 ↔ lt (len lst1) (len lst2) := iff.rfl

-- it should be easier than this, right? how on earth do I just say
-- "because < is well-founded".
theorem shorter_well_founded: well_founded (@shorter T) :=
begin
  split,
  -- can't figure out how to use "generalizing"
  suffices h:
    ∀ a: mylist T,
      ∀ n,
        n = len a → acc shorter a, {
    intro a,
    from h a (len a) rfl,
  }, {
    intros a n, revert n a,
    assume hnla,
    apply strict_strong_induction
        (λ n, ∀ a : mylist T, n = len a → acc shorter a), {
      intro n,
      assume h_ih,
      intro a,
      assume hnla,
      split,
      intro y,
      assume hysa,
      rw [shorter_lt, ←hnla] at hysa,
      from h_ih (len y) hysa y rfl,
    },
  },
end

-- this made the red lines go away
namespace lwf

instance: has_well_founded (mylist T) :=
  ⟨shorter, shorter_well_founded⟩

end lwf

-- attempts at defining things that recurse on the init

-- private def lst_is_odd: mylist T → Prop
-- | empty := false
-- | (x :: xs) := have shorter (init (x :: xs) (cons_not_empty)) (x :: xs),
--                from begin
--                       rw shorter_lt,
--                       have: ∀ x y, lt x y ↔ x < y := (λ x y, iff.rfl),
--                       rw this,
--                       rw lt_iff_succ_le,
--                       rw ←len_init,
--                       from le_refl,
--                     end,
--                ¬lst_is_odd (init (x :: xs) (cons_not_empty))

-- TODO: make this work
-- def palindrome: mylist T → Prop
-- | empty             := true
-- | (x :: empty)      := true
-- | (x :: y :: xs) := x = last (y :: xs) (cons_not_empty _ _)
--                   ∧ palindrome (init (y :: xs) (cons_not_empty _ _))

end mylist
end hidden
