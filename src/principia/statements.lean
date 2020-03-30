import principia.parity

-- This file is specifically for statements of famous theorems.
-- It is a useful and fun thing to state these, but they're better off in a
-- different file because they tend to use sorry

namespace hidden

open mynat

-- Landau's Problems about prime numbers
-- https://en.wikipedia.org/wiki/Landau%27s_problems
theorem goldbachs_conjecture {m : mynat} :
even m → ∃ p q: mynat, prime p → prime q → p + q = m :=
sorry

theorem twin_prime_conjecture:
infinitely_many (λ p, prime p ∧ prime (p+2)) := sorry

theorem legendres_conjecture {m : mynat} :
∃ p, m*m ≤ p ∧ p ≤ (m+1)*(m+1) ∧ prime p := sorry

theorem landau4:
infinitely_many (λ n, prime (n*n + 1)) := sorry

end hidden
