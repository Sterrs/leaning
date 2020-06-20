import .hcf
import ..quotint.dvd

namespace hidden

open quotint

namespace mynat

theorem bezouts_lemma_coprime {m n : mynat} :
coprime m n → ∃ x y : quotint, ↑m * x + ↑n * y = 1 :=
begin
  sorry,
end

theorem euclids_lemma_v2 {p m n: mynat} : prime p → p ∣ m * n → p ∣ m ∨ p ∣ n :=
begin
  sorry
end

-- Requires some form of FTA
theorem dvd_coprime {m n k : mynat}:
coprime m n → m ∣ k * n → m ∣ k := sorry

theorem coprime_imp_prod_dvd {m n k : mynat}:
coprime m n → m ∣ k → n ∣ k → m * n ∣ k :=
begin
  assume hcp hmk hnk,
  cases hmk with a ha,
  cases hnk with b hb,
  rw hb at ha,
  have hmb : m ∣ b,
    have hmprod : m ∣ b * n,
      rw [ha, mul_comm],
      apply dvd_mul,
      from dvd_refl,
    apply dvd_coprime,
    repeat {assumption},
  cases hmb with c hc,
  rw [hc, mul_assoc] at hb,
  existsi c, assumption,
end

-- Could go on to state and prove FTA via multisets

end mynat
end hidden
