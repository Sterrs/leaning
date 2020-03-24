import naturals.mynat

-- TODO:
-- think of a nice way to do "maybe" operations like indexing,
-- inserting, deleting

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

end hidden
