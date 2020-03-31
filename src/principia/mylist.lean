import principia.mynat
import principia.lt

namespace hidden

universe u

-- list of elements of type T
inductive mylist (T: Type u)
-- allow empty to infer its type. It doesn't seem to work very often
| empty {}: mylist
| cons (head: T) (tail: mylist): mylist

open mylist
open mynat

variable {T: Type u}
-- Haskell-like convention, use x::xs to pattern match head/tail
variables x y z: T
variables xs ys zs lst lst1 lst2 lst3: mylist T
variables m n: mynat

-- I'm really just sort of making this up as I go along
-- It would be nice to have notation like [1, 2, 3]
notation h :: t := cons h t
notation `[]` := empty
def singleton := x :: ([]: mylist T)
-- is this bad practice? Am I overriding some important other notation??
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

-- we don't define append explicitly, since lists are define by recursion on the
-- tail. Also note that concat is defined by recursion on the first argument, so
-- you should generally induct on the first argument.
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

@[simp]
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
    simp [lst_ih],
  },
end

theorem rev_len: len lst = len (rev lst) :=
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
  repeat {rw ←rev_len},
  assume h, from h,
end

-- These are some "maybe" operations, which are undefined on empty lists
-- (or sometimes lists of a certain length), so they take as argument
-- a proof that the input list is of the correct form,
-- which is a dependent type thing. Maybe they're supposed to be Πs

-- first element
def head: ∀ lst: mylist T, lst ≠ [] → T
| []       h := absurd rfl h
| (x :: _) _ := x

@[simp] theorem first_cons (h: x :: xs ≠ []): head (x :: xs) h = x := rfl

-- everything except first element
def tail: ∀ lst: mylist T, lst ≠ [] → mylist T
| []        h := absurd rfl h
| (_ :: xs) _ := xs

@[simp] theorem tail_cons (h: x :: xs ≠ []): tail (x :: xs) h = xs := rfl

-- everything except last element
def init: ∀ lst: mylist T, lst ≠ [] → mylist T
| []             h := absurd rfl h
| (x :: [])      _ := []
| (x :: y :: xs) _ := x :: init (y :: xs) (cons_not_empty _ _ )

@[simp]
theorem init_singleton (h: [x] ≠ []): init [x] h = [] := rfl
@[simp]
theorem init_ccons (h: x :: y :: xs ≠ []):
init (x :: y :: xs) h = x :: init (y :: xs) (cons_not_empty _ _) := rfl

-- last element
def last: ∀ lst: mylist T, lst ≠ [] → T
| []             h := absurd rfl h
| (x :: [])      _ := x
| (x :: y :: xs) h := last (y :: xs) (cons_not_empty _ _)

@[simp]
theorem last_singleton (h: [x] ≠ []): last [x] h = x := rfl
@[simp]
theorem last_ccons (h: x :: y :: xs ≠ []):
last (x :: y :: xs) h = last (y :: xs) (cons_not_empty _ _) := rfl

private theorem len_cons_succ_cancel1 (h: succ n ≤ len (x :: xs)): n ≤ len xs :=
begin
  simp at h,
  from le_succ_cancel _ _ h,
end

private theorem absurd_succ_le_zero: ¬succ n ≤ 0 :=
begin
  assume h,
  simp [le_iff_lt_succ] at h,
  exfalso, from lt_nzero _ (lt_succ_cancel _ _ h),
end

-- the first n elements
def take: ∀ n: mynat, ∀ lst: mylist T, n ≤ len lst → mylist T
| 0        _         _ := []
| (succ n) []        h := absurd h (absurd_succ_le_zero n)
| (succ n) (x :: xs) h := x :: take n xs (len_cons_succ_cancel1 _ _ _ h)

@[simp] theorem take_zero (h: 0 ≤ len lst): take 0 lst h = [] := rfl
@[simp]
theorem take_succ_cons
(h: succ n ≤ len (x :: xs)):
take (succ n) (x :: xs) h = x :: take n xs (len_cons_succ_cancel1 _ _ _ h) := rfl

-- everything except the first n elements
def drop: ∀ n: mynat, ∀ lst: mylist T, n ≤ len lst → mylist T
| 0        lst       _ := lst
| (succ n) []        h := absurd h (absurd_succ_le_zero n)
| (succ n) (_ :: xs) h := drop n xs (len_cons_succ_cancel1 _ _ _ h)

@[simp] theorem drop_zero (h: 0 ≤ len lst): drop 0 lst h = lst := rfl
@[simp]
theorem drop_succ_cons
(h: succ n ≤ len (x :: xs)):
drop (succ n) (x :: xs) h = drop n xs (len_cons_succ_cancel1 _ _ _ h) := rfl

private theorem len_cons_succ_cancel2 (h: succ n < len (x :: xs)): n < len xs :=
begin
  simp at h,
  from lt_succ_cancel _ _ h,
end

-- the nth element
def get: ∀ n: mynat, ∀ lst: mylist T, n < len lst → T
| n        []        h := absurd h (lt_nzero n)
| 0        (x :: _)  _ := x
| (succ n) (x :: xs) h := get n xs (len_cons_succ_cancel2 _ _ _ h)

@[simp]
theorem get_zero_cons
(h: 0 < len (x :: xs)):
get 0 (x :: xs) h = x := rfl

@[simp]
theorem get_succ_cons
(h: succ n < len (x :: xs)):
get (succ n) (x :: xs) h = get n xs (len_cons_succ_cancel2 _ _ _ h) := rfl

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
      have hi := init_singleton _ h,
      simp at hi,
      rw hi,
    }, {
      apply lst_ih,
    },
  },
end

theorem append_init_last (h: lst ≠ []): init lst h ++ [last lst h] = lst :=
begin
  induction lst, {
    from absurd rfl h,
  }, {
    cases lst_tail, {
      have hi := init_singleton _ h,
      simp at hi,
      rw hi,
      have hl := last_singleton _ h,
      simp at hl,
      rw hl,
      simp,
    }, {
      rw init_ccons _ _ _ h,
      rw last_ccons _ _ _ h,
      simp,
      apply lst_ih,
    },
  },
end

-- TODO: get_n_head_drop, len_drop, len_take, concat_drop_take, concat_cancel, rev_take_drop

private theorem succ_le_impl_le (h: succ n ≤ len lst): n ≤ len lst :=
(le_cancel_strong n (len lst) 1 h)

-- theorem drop_init (h: succ n ≤ len lst) :=
-- drop (succ n) lst h = init (drop n lst (succ_le_impl_le _ _ h))
-- begin

-- end :=
-- begin
  
-- end

-- theorem len_drop_succ (h: succ n ≤ len lst):
-- succ (len (drop (succ n) lst h))
--   = len (drop n lst (succ_le_impl_le _ _ h)) :=
-- begin
--   cases lst, {
--     exfalso, from succ_ne_zero _ (le_zero _ h),
--   }, {
--     rw drop_succ_cons,
--     induction n, {
--       simp,
--     }, {
--       simp,
--       sorry,
--     },
--   },
-- end

@[simp]
theorem len_take_succ (h: succ n ≤ len lst):
len (take (succ n) lst h)
  = succ (len (take n lst (succ_le_impl_le _ _ h))) :=
begin
  revert lst,
  induction n, {
    intro lst,
    assume h,
    simp,
    cases lst, {
      exfalso,
      simp at h, -- clearly absurd. Is there a quicker way?
      cases h with d hd,
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
      rw take_succ_cons lst_head lst_tail 0,
      simp,
    },
  }, {
    intro lst,
    assume h,
    cases lst, {
      exfalso,
      cases h with d hd,
      from mynat.no_confusion (add_integral hd.symm),
    }, {
      simp,
      rw len_cons_succ at h,
      from n_ih lst_tail (le_succ_cancel _ _ h),
    },
  },
end

theorem len_take (h: n ≤ len lst): len (take n lst h) = n :=
begin
  induction n, {
    simp,
  }, {
    -- really all the hard work happens in len_take_succ
    simp,
    apply n_ih,
  },
end

def contains: T → mylist T → Prop
| _ []        := false
| x (y :: ys) := x = y ∨ contains x ys

instance: has_mem T (mylist T) := ⟨contains⟩

theorem contains_cons: x ∈ (y :: ys) ↔ x = y ∨ x ∈ ys := iff.rfl
theorem singleton_contains: x ∈ [x] := (contains_cons x x []).mpr (or.inl rfl)

-- TODO: make this work
-- def palindrome: mylist T → Prop
-- | []             := true
-- | (x :: [])      := true
-- | (x :: y :: xs) := x = last (y :: xs) (cons_not_empty _ _)
--                   ∧ palindrome (init (y :: xs) (cons_not_empty _ _))

end hidden
