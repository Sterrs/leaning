-- vim: ts=2 sw=0 sts=-1 et ai tw=70

import .mynat.parity
import .mynat.sum

-- This file is specifically for statements of famous theorems.
-- It is a useful and fun thing to state these, but they're better off
-- in a different file because they tend to use sorry

open hidden.mynat
open hidden

-- Landau's Problems about prime numbers
-- https://en.wikipedia.org/wiki/Landau%27s_problems
theorem goldbachs_conjecture {m : mynat} :
even m → ∃ p q: mynat, prime p → prime q → p + q = m := sorry

theorem twin_prime_conjecture:
infinitely_many (λ p, prime p ∧ prime (p+2)) := sorry

theorem legendres_conjecture {m : mynat} :
∃ p, m*m ≤ p ∧ p ≤ (m+1)*(m+1) ∧ prime p := sorry

theorem landau4:
infinitely_many (λ n, prime (n*n + 1)) := sorry

-- instructive exercise in disproof by counterexample
theorem fermats_penultimate_theorem:
¬ ∀ a b c n: mynat, a^n + b^n = c^n → n = 2 :=
begin
  assume hflt,
  have h := hflt 1 1 2 1 rfl,
  cases h,
end

theorem fermats_last_theorem (a b c n: mynat):
a ≠ 0 → b ≠ 0 → a ^ n + b ^ n = c ^ n → n = 1 ∨ n = 2 := sorry

def collatz_sequence : mynat → sequence mynat
| m zero     := m
| m (succ n) :=
begin
  have prev := collatz_sequence m n,
  exact
  if even prev then
    sorry -- Need division
  else
    3 * prev + 1,
end

-- "Mathematics may not be ready for such problems"
theorem collatz_conjecture:
∀ m, ∃ n, collatz_sequence m n = 1 := sorry
