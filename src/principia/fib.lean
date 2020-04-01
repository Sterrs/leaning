import .mynat
import .dvd
import .induction

namespace hidden

open mynat

-- it's kind of crazy that Lean just automatically proves this is well-defined
-- (try changing fib succ to fib succ succ)
def fib: mynat → mynat
| 0               := 0
| 1               := 1
| (succ (succ n)) := fib n + fib (succ n)

variables {m n k p: mynat}

-- what is the general tactical way to say to lean "just evaluate this constant
-- sub-expression please"?
@[simp] theorem fib_zero: fib 0 = 0 := rfl
@[simp] theorem fib_one: fib 1 = 1 := rfl
@[simp] theorem fib_succsucc: fib (succ (succ n)) = fib n + fib (succ n) := rfl

theorem fib_k_formula (k: mynat):
fib (m + (k + 1)) = fib k * fib m + fib (k + 1) * fib (m + 1) :=
begin
  -- this is here because I retroactively changed the theorem statement
  -- and I'm lazy
  rw ←add_assoc,
  revert k,
  apply duo_induction, {
    simp,
  }, {
    simp,
    refl,
  }, {
    intro k,
    assume h_ih1 h_ih2,
    -- yucky algebra
    have: (2: mynat) = 1 + 1 := rfl,
    rw this,
    repeat {rw ←add_assoc},
    rw [add_one_succ, add_one_succ],
    rw fib_succsucc,
    rw ←add_one_succ,
    rw ←add_assoc at h_ih2,
    rw [h_ih1, h_ih2],
    -- now we have to collect the terms in F_m and F_{m + 1}
    conv {
      to_lhs,
      rw add_assoc,
      rw add_comm,
      congr, congr, skip,
      rw add_comm,
    },
    rw ←add_assoc,
    rw ←add_mul,
    conv {
      to_lhs,
      congr, congr, congr, congr, skip,
      rw add_one_succ,
    },
    rw ←fib_succsucc,
    rw add_assoc,
    rw ←add_mul,
    conv {
      to_lhs,
      congr, skip, congr,
      rw add_comm,
      rw add_one_succ,
    },
    rw ←fib_succsucc,
    rw add_comm,
    refl,
  },
end

-- this is a consequence of the big one we want to prove, which is
-- F_gcd(m, n) = gcd(F_m, F_n), which actually needs only fairly basic
-- properties of gcd - but it does require that you've defined gcd, sadly.
theorem f_preserves_multiples
(k: mynat):
n ∣ m → fib n ∣ fib m :=
begin
  assume hnm,
  cases hnm with k hk,
  cases n, {
    rw hk,
    simp,
  }, {
    rw [hk, mul_comm],
    clear hk,
    induction k with k_n k_ih, {
      from dvd_zero,
    }, {
      rw [mul_succ, add_comm],
      conv {
        congr, skip, congr, congr, skip,
        rw ←add_one_succ,
      },
      rw [fib_k_formula n, add_one_succ],
      apply dvd_sum, {
        rw mul_comm,
        from dvd_mul _ k_ih,
      }, {
        rw mul_comm,
        from dvd_multiple,
      },
    },
  },
end

-- TODO: coprime theorem

-- induction, just to see if I could, really.
-- the nice high-level way to prove this is using determinants
theorem cassini_odd:
fib (2 * n) * fib (2 * n + 2) + 1
  = fib (2 * n + 1) * fib (2 * n + 1) :=
begin
  have cancel2: ∀ a b c: mynat, a = b → c + a = c + b, {
    intros, rw a_1,
  },
  induction n with n hn, {
    refl,
  }, {
    repeat {rw mul_succ},
    have h2k: ∀ k: mynat, 2 + k = succ (succ k), {
      intro k,
      rw add_comm,
      refl,
    },
    repeat {rw h2k},
    have hk2: ∀ k: mynat, k + 2 = succ (succ k), {
      intro k, refl,
    },
    repeat {rw hk2},
    repeat {rw add_one_succ},
    repeat {rw fib_succsucc},
    repeat {rw ←add_one_succ}, -- legibility
    repeat {rw mul_add},
    repeat {rw add_mul},
    -- laboriously cancel terms. This is likely very inefficient algebra,
    -- but it's hard for me to keep track of things otherwise.
    -- Lots of conv, for similar reasons
    conv {
      to_lhs,
      congr,
      rw [←add_assoc, ←add_assoc, ←add_assoc, ←add_assoc, ←add_assoc,
          ←add_assoc],
      rw add_comm,
    },
    repeat {rw add_assoc},
    apply cancel2,
    repeat {rw ←add_assoc},
    rw add_comm (fib (2 * n) * fib (2 * n)),
    repeat {rw add_assoc},
    rw mul_comm,
    apply cancel2,
    repeat {rw ←add_assoc},
    rw add_comm (fib (2 * n) * fib (2 * n)),
    repeat {rw add_assoc},
    conv {
      to_rhs,
      rw add_comm,
    },
    repeat {rw add_assoc},
    apply cancel2,
    apply cancel2,
    repeat {rw ←add_assoc},
    rw add_comm (fib (2 * n + 1) * fib (2 * n + 1)),
    repeat {rw add_assoc},
    apply cancel2,
    apply cancel2,
    conv {
      to_rhs,
      rw add_comm,
      rw add_assoc,
    },
    apply cancel2,
    conv {
      congr,
      rw add_comm,
      rw add_assoc,
      skip,
      rw add_comm,
    },
    apply cancel2,
    conv {
      to_lhs,
      rw add_comm,
      rw ←add_assoc,
      rw ←mul_add,
      congr,
      rw add_one_succ,
      rw ←fib_succsucc,
    },
    from hn,
  },
end

theorem cassini_even:
fib (2 * n + 1) * fib (2 * n + 3)
  = fib (2 * n + 2) * fib (2 * n + 2) + 1 :=
begin
  have cancel2: ∀ a b c: mynat, a = b → c + a = c + b, {
    intros, rw a_1,
  },
  repeat {rw mul_succ},
  have h2k: ∀ k: mynat, 2 + k = succ (succ k), {
    intro k,
    rw add_comm,
    refl,
  },
  repeat {rw h2k},
  have hk2: ∀ k: mynat, k + 2 = succ (succ k), {
    intro k, refl,
  },
  repeat {rw hk2},
  have hk3: ∀ k: mynat, k + 3 = succ (succ (succ k)), {
    intro k, refl,
  },
  repeat {rw hk3},
  repeat {rw add_one_succ},
  repeat {rw fib_succsucc},
  repeat {rw ←add_one_succ}, -- legibility
  repeat {rw mul_add},
  repeat {rw add_mul},

  repeat {rw add_assoc},
  conv {
    congr,
    rw add_comm,
    skip,
    rw add_comm,
  },
  repeat {rw add_assoc},
  apply cancel2,
  conv {
    to_rhs,
    rw add_comm,
  },
  repeat {rw add_assoc},
  apply cancel2,
  conv {
    to_rhs,
    rw add_comm,
    congr,
    rw ←mul_add,
    rw add_one_succ,
    rw ←fib_succsucc,
  },
  from cassini_odd.symm,
end

end hidden
