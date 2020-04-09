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

variable {T: Sort u}
-- Haskell-like convention, use x::xs to pattern match head/tail
variables {x y z: T}
variables {xs ys zs lst lst1 lst2 lst3: mylist T}
variables {m n: mynat}

-- I'm really just sort of making this up as I go along
-- It would be nice to have notation like [1, 2, 3]
notation h :: t := cons h t
notation `[]` := empty
def singleton (x: T) := x :: ([]: mylist T)
-- is this bad practice? Am I overriding some important other
-- notation??
notation `[`x`]` := singleton x

@[simp] theorem singleton_cons_empty: [x] = x :: [] := rfl

theorem cons_injective_1: x :: xs = y :: ys → x = y :=
begin
  assume h,
  cases h,
  refl,
end

theorem cons_injective_2: x :: xs = y :: ys → xs = ys :=
begin
  assume h,
  cases h,
  refl,
end

-- we don't define append explicitly, since lists are define by
-- recursion on the tail. Also note that concat is defined by
-- recursion on the first argument, so you should generally induct on
-- the first argument.
def concat: mylist T → mylist T → mylist T
| []        lst := lst
| (x :: xs) lst := x :: (concat xs lst)

notation lst1 ++ lst2 := concat lst1 lst2

@[simp] theorem empty_concat: ([]: mylist T) ++ lst = lst := rfl
@[simp]
theorem cons_concat: (x :: xs) ++ lst = x :: (xs ++ lst) := rfl

@[simp]
theorem concat_empty: lst ++ ([]: mylist T) = lst :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    simp,
  }, {
    simp [lst_ih],
  },
end

@[simp]
theorem singleton_concat_cons: [x] ++ lst = x :: lst := rfl

@[simp]
theorem cons_not_empty: x :: xs ≠ [] :=
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

def len: mylist T → mynat
| []        := 0
| (_ :: xs) := succ (len xs)

@[simp]
theorem empty_len: len ([]: mylist T) = 0 := rfl

@[simp]
theorem len_cons_succ: len (x :: xs) = succ (len xs) := rfl

@[simp]
theorem len_singleton: len [x] = 1 := len_cons_succ

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
| []        := []
| (x :: xs) := (rev xs) ++ [x]

@[simp] theorem rev_empty: rev ([]: mylist T) = [] := rfl
@[simp] theorem rev_cons: rev (x :: xs) = (rev xs) ++ [x] := rfl
@[simp] theorem rev_singleton: rev [x] = [x] := rfl

@[simp]
theorem rev_append: rev (lst ++ [x]) = x :: rev lst :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    simp,
  }, {
    rw [cons_concat, rev_cons, lst_ih],
    simp,
  },
end

theorem rev_concat: rev (lst1 ++ lst2) = rev lst2 ++ rev lst1 :=
begin
  induction lst1 with lst1_head lst1_tail lst1_ih, {
    simp,
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

theorem nonempty_iff_len: lst ≠ [] ↔ len lst ≠ 0 :=
begin
  cases lst, {
    simp,
  }, {
    simp,
    from succ_ne_zero,
  },
end

theorem rev_not_empty: lst ≠ [] → rev lst ≠ [] :=
begin
  repeat {rw nonempty_iff_len},
  rw rev_len,
  assume h, from h,
end

-- These are some "maybe" operations, which are undefined on empty lists
-- (or sometimes lists of a certain length), so they take as argument
-- a proof that the input list is of the correct form,
-- which is a dependent type thing. Maybe they're supposed to be Πs

-- first element
def head: Π lst: mylist T, lst ≠ [] → T
| []       h := absurd rfl h
| (x :: _) _ := x

@[simp] theorem first_cons (h: x :: xs ≠ []): head (x :: xs) h = x := rfl

-- everything except first element
def tail: Π lst: mylist T, lst ≠ [] → mylist T
| []        h := absurd rfl h
| (_ :: xs) _ := xs

@[simp] theorem tail_cons (h: x :: xs ≠ []): tail (x :: xs) h = xs := rfl

-- everything except last element
def init: Π lst: mylist T, lst ≠ [] → mylist T
| []             h := absurd rfl h
| (x :: [])      _ := []
| (x :: y :: xs) _ := x :: init (y :: xs) cons_not_empty

@[simp]
theorem init_singleton (h: [x] ≠ []): init [x] h = [] := rfl
@[simp]
theorem init_ccons (h: x :: y :: xs ≠ []):
init (x :: y :: xs) h = x :: init (y :: xs) cons_not_empty := rfl

-- last element
def last: Π lst: mylist T, lst ≠ [] → T
| []             h := absurd rfl h
| (x :: [])      _ := x
| (x :: y :: xs) h := last (y :: xs) cons_not_empty

@[simp]
theorem last_singleton (h: [x] ≠ []): last [x] h = x := rfl
@[simp]
theorem last_ccons (h: x :: y :: xs ≠ []):
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
| 0        _         _ := []
| (succ n) []        h := absurd h absurd_succ_le_zero
| (succ n) (x :: xs) h := x :: take n xs (len_cons_succ_cancel1 h)

@[simp] theorem take_zero (h: 0 ≤ len lst): take 0 lst h = [] := rfl

@[simp]
theorem take_succ_cons
(h: succ n ≤ len (x :: xs)):
take (succ n) (x :: xs) h
  = x :: take n xs (len_cons_succ_cancel1 h) := rfl

-- everything except the first n elements
def drop: Π n: mynat, Π lst: mylist T, n ≤ len lst → mylist T
| 0        lst       _ := lst
| (succ n) []        h := absurd h absurd_succ_le_zero
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
| n        []        h := absurd h lt_nzero
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

theorem cons_head_tail (h: lst ≠ []): head lst h :: tail lst h = lst :=
begin
  cases lst, {
    contradiction,
  }, {
    simp,
  },
end

theorem len_tail (h: lst ≠ []): len lst = succ (len (tail lst h)) :=
begin
  cases lst, {
    contradiction,
  }, {
    simp,
  },
end

-- I didn't really think this one through
theorem len_init (h: lst ≠ []): len lst = succ (len (init lst h)) :=
begin
  induction lst, {
    contradiction,
  }, {
    simp,
    cases lst_tail, {
      have hi := init_singleton h,
      simp at hi,
      rw hi,
    }, {
      apply lst_ih,
    },
  },
end

theorem append_init_last (h: lst ≠ []):
init lst h ++ [last lst h] = lst :=
begin
  induction lst, {
    from absurd rfl h,
  }, {
    cases lst_tail, {
      have hi := init_singleton h,
      simp at hi,
      rw hi,
      have hl := last_singleton h,
      simp at hl,
      rw hl,
      simp,
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

-- we could of course deduce that n ≤ len lst from hsnl,
-- but then this theorem would be less general. This way, we
-- show this theorem holds for all proofs of n ≤ len lst.
theorem len_take_succ
(hsnl: succ n ≤ len lst)
(hnl: n ≤ len lst):
len (take (succ n) lst hsnl)
  = succ (len (take n lst hnl)) :=
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
      rw len_cons_succ at hnl,
      from n_ih (le_succ_cancel hsnl) (le_succ_cancel hnl),
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
    simp [len_take_succ _ (succ_le_impl_le hnl)],
    apply n_ih,
  },
end

theorem take_concat_drop (hnl_1 hnl_2: n ≤ len lst):
take n lst hnl_1 ++ drop n lst hnl_2 = lst :=
begin
  induction n generalizing lst, {
    refl,
  }, {
    cases lst, {
      simp at hnl_1,
      cases hnl_1 with d hd,
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
(hnld: n ≤ len lst)
(hnlg: n < len lst)
(hdne: drop n lst hnld ≠ []):
get n lst hnlg = head (drop n lst hnld) hdne :=
begin
  induction n generalizing lst, {
    simp,
  }, {
    cases lst, {
      exfalso, from lt_nzero hnlg,
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

-- the obvious facts that show that these operations don't depend
-- on how you prove the list is long enough.
theorem head_h_irrelev
(hnl_1 hnl_2: lst ≠ []):
head lst hnl_1 = head lst hnl_2 :=
begin
  cases lst, {
    contradiction,
  }, {
    refl,
  },
end

theorem tail_h_irrelev
(hnl_1 hnl_2: lst ≠ []):
tail lst hnl_1 = tail lst hnl_2 :=
begin
  cases lst, {
    contradiction,
  }, {
    refl,
  },
end

theorem last_h_irrelev
(hnl_1 hnl_2: lst ≠ []):
last lst hnl_1 = last lst hnl_2 :=
begin
  cases lst, {
    contradiction,
  }, {
    refl,
  },
end

theorem init_h_irrelev
(hnl_1 hnl_2: lst ≠ []):
init lst hnl_1 = init lst hnl_2 :=
begin
  cases lst, {
    contradiction,
  }, {
    refl,
  },
end

theorem take_h_irrelev
(hnl_1 hnl_2: n ≤ len lst):
take n lst hnl_1 = take n lst hnl_2 := rfl

theorem drop_h_irrelev
(hnl_1 hnl_2: n ≤ len lst):
drop n lst hnl_1 = drop n lst hnl_2 := rfl

theorem get_h_irrelev
(hnl_1 hnl_2: n < len lst):
get n lst hnl_1 = get n lst hnl_2 := rfl

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
theorem drop_all (h: len lst ≤ len lst): drop (len lst) lst h = [] :=
begin
  induction lst with lst_head lst_tail lst_ih, {
    refl,
  }, {
    simp,
    from lst_ih _,
  },
end

theorem take_idem
(hml_1 hml_3: m ≤ len lst)
(hml_2: m ≤ len (take m lst hml_1)):
take m (take m lst hml_1) hml_2 = take m lst hml_3 :=
begin
  induction m with m hm generalizing lst, {
    refl,
  }, {
    cases lst, {
      exfalso,
      from lt_nzero (lt_iff_succ_le.mpr hml_1),
    }, {
      simp,
      apply hm,
    },
  },
end

theorem take_take
(hml: m ≤ len lst)
(hnl_1: n ≤ len (take m lst hml))
(hnl_2: n ≤ len lst):
take n (take m lst hml) hnl_1 = take n lst hnl_2 :=
begin
  induction n with n hn generalizing m lst, {
    refl,
  }, {
    cases lst, {
      exfalso,
      from lt_nzero (lt_iff_succ_le.mpr hnl_2),
    }, {
      cases m, {
        exfalso,
        simp at hnl_1,
        from lt_nzero (lt_iff_succ_le.mpr hnl_1),
      }, {
        simp,
        apply hn,
      },
    },
  },
end

theorem drop_drop
(hml: m ≤ len lst)
(hnl: n ≤ len (drop m lst hml))
(hmnl: m + n ≤ len lst):
drop n (drop m lst hml) hnl = drop (m + n) lst hmnl :=
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
(h1l: 1 ≤ len lst)
(hne: lst ≠ []):
drop 1 lst h1l = tail lst hne :=
begin
  cases lst, {
    refl,
  }, {
    refl,
  },
end

theorem take_init
(hnl: len xs ≤ len (xs ++ [x])):
take (len xs) (xs ++ [x]) hnl = xs :=
begin
  induction xs, {
    refl,
  }, {
    simp,
    apply xs_ih,
  },
end

theorem take_ignore
(hnl_1: n ≤ len (xs ++ [x]))
(hnl_2: n ≤ len xs):
take n (xs ++ [x]) hnl_1 = take n xs hnl_2 :=
begin
  suffices h:
      take n (take (len xs) (xs ++ [x]) _) _ = take n xs hnl_2, {
    rw @take_take _ (xs ++ [x]) (len xs) n _ _ _ at h,
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
(hml: m ≤ len lst)
(hnlr: n ≤ len (rev lst))
(hmn: m + n = len lst):
drop m lst hml = rev (take n (rev lst) hnlr) :=
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
      exfalso, from lt_nzero (lt_iff_succ_le.mpr hml),
    }, {
      rw drop_succ_cons,
      simp at hml,
      have := hm (le_succ_cancel hml) _ _, {
        rw this,
        conv in (rev (lst_head :: lst_tail)) {rw rev_cons},
        rw take_ignore,
      }, {
        existsi m,
        rw rev_len,
        simp at hmn,
        rw [←hmn, add_comm],
      }, {
        simp at hmn,
        rw [←hmn, add_comm],
      },
    },
  },
end

-- for some reason this has to be a Type ???
-- otherwise has_mem complains
variable {T': Type u}
variables {x' y' z': T'}
variables {xs' ys' zs': mylist T'}

def contains: T' → mylist T' → Prop
| _ []           := false
| x' (y' :: ys') := x' = y' ∨ contains x' ys'

instance: has_mem T' (mylist T') := ⟨contains⟩

theorem contains_cons: x' ∈ (cons y' ys') ↔ x' = y' ∨ x' ∈ ys' := iff.rfl
theorem singleton_contains: x' ∈ [x'] := contains_cons.mpr (or.inl rfl)

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
-- | [] := false
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
-- | []             := true
-- | (x :: [])      := true
-- | (x :: y :: xs) := x = last (y :: xs) (cons_not_empty _ _)
--                   ∧ palindrome (init (y :: xs) (cons_not_empty _ _))

end hidden
