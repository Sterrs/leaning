import .mylist

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

end hidden
