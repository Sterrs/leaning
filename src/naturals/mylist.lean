import naturals.mynat
import naturals.lt

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
| [] lst        := lst
| (x :: xs) lst := x :: (concat xs lst)

notation lst1 ++ lst2 := concat lst1 lst2

@[simp] theorem empty_concat: ([]: mylist T) ++ lst = lst := rfl
@[simp]
theorem cons_concat: (x :: xs) ++ lst = x :: (xs ++ lst) := rfl

@[simp]
theorem concat_empty: lst ++ ([]: mylist T) = lst :=
begin
  induction lst, {
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
  induction lst1, {
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
  induction lst1, {
    simp,
  }, {
    simp [lst1_ih],
  }
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
  induction lst, {
    simp,
  }, {
    rw [cons_concat, rev_cons, lst_ih],
    simp,
  },
end

@[simp]
theorem rev_concat: rev (lst1 ++ lst2) = rev lst2 ++ rev lst1 :=
begin
  induction lst1, {
    simp,
  }, {
    rw [cons_concat, rev_cons, lst1_ih, rev_cons, concat_assoc],
  },
end

@[simp]
theorem rev_rev: rev (rev lst) = lst :=
begin
  induction lst, {
    simp,
  }, {
    simp [lst_ih],
  },
end

theorem rev_len: len lst = len (rev lst) :=
begin
  induction lst, {
    simp,
  }, {
    simp [lst_ih],
  }
end

theorem nonempty_iff_len: lst ≠ [] ↔ len lst ≠ 0 :=
begin
  cases lst, {
    simp,
  }, {
    simp,
    from succ_ne_zero (len lst_tail),
  }
end

theorem nonempty_iff_cons: lst ≠ [] ↔ ∃ x: T, ∃ xs: mylist T, lst = x :: xs :=
begin
  cases lst, {
    simp,
    assume h,
    cases h with _ h,
    cases h with _ h,
    assumption,
  }, {
    simp,
    existsi lst_head,
    existsi lst_tail,
    simp,
  },
end

theorem rev_not_empty: lst ≠ [] → rev lst ≠ [] :=
begin
  repeat {rw nonempty_iff_len},
  repeat {rw ←rev_len},
  assume h, from h,
end

def first: ∀ lst: mylist T, lst ≠ [] → T
| []        h := absurd rfl h
| (x :: xs) _ := x

def tail: ∀ lst: mylist T, lst ≠ [] → mylist T
| []        h := absurd rfl h
| (x :: xs) _ := xs

def init: ∀ lst: mylist T, lst ≠ [] → mylist T
| []             h := absurd rfl h
| (x :: [])      _ := []
| (x :: y :: xs) _ := x :: init (y :: xs) (cons_not_empty _ _ )

@[simp]
theorem init_singleton (h: [x] ≠ []): init [x] h = [] := rfl
@[simp]
theorem init_ccons (h: x :: y :: xs ≠ []):
init (x :: y :: xs) h = x :: init (y :: xs) (cons_not_empty _ _) := rfl

def last: ∀ lst: mylist T, lst ≠ [] → T
| []             h := absurd rfl h
| (x :: [])      _ := x
| (x :: y :: xs) h := last (y :: xs) (cons_not_empty _ _)

@[simp]
theorem last_singleton (h: [x] ≠ []): last [x] h = x := rfl
@[simp]
theorem last_ccons (h: x :: y :: xs ≠ []):
last (x :: y :: xs) h = last (y :: xs) (cons_not_empty _ _) := rfl

def get: ∀ lst: mylist T, ∀ n: mynat, n < len lst → T
| []        n        h := begin
                            simp at h, exfalso, from lt_nzero _ h,
                          end
| (x :: xs) 0        h := x
| (x :: xs) (succ n) h := get xs n begin
                                     simp at h, from lt_succ_cancel _ _ h,
                                   end

theorem concat_init_last (h: lst ≠ []): init lst h ++ [last lst h] = lst :=
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
    }
  },
end

-- TODO: make this work
-- def palindrome: mylist T → Prop
-- | []             := true
-- | (x :: [])      := true
-- | (x :: y :: xs) := x = last (y :: xs) (cons_not_empty _ _)
--                   ∧ palindrome (init (y :: xs) (cons_not_empty _ _))

end hidden
