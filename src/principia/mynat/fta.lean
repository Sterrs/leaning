import .hcf
import ..myint.dvd
import ..logic

namespace hidden

open myint

namespace mynat

theorem coprime_imp_either_nzero {m n : mynat} (h : coprime m n) :
m ≠ 0 ∨ n ≠ 0 :=
begin
  by_contradiction h0,
  rw [not_or_distrib, not_not, not_not] at h0,
  cases h0 with hm hn,
  subst hm, subst hn,
  unfold coprime at h,
  suffices : (0 : mynat) = 1,
    from mynat.no_confusion this,
  apply h; from dvd_refl,
end

theorem coprime_imp_hcf_one {m n : mynat} (h : coprime m n) :
hcf m n = 1 :=
begin
  apply h,
    from hcf_dvd_left _ _ (coprime_imp_either_nzero h),
  from hcf_dvd_right _ _ (coprime_imp_either_nzero h),
end

theorem bezouts_lemma_coprime {m n : mynat} (h : coprime m n):
∃ x y : myint, ↑m * x + ↑n * y = 1 :=
begin
  rw [←coe_one, bezouts_lemma (coprime_imp_either_nzero h), coprime_imp_hcf_one h],
  from dvd_refl,
end

open classical

local attribute [instance] prop_decidable

theorem euclids_lemma {p m n: mynat} (hp : prime p) : p ∣ m * n → p ∣ m ∨ p ∣ n :=
begin
  assume h,
  by_cases p ∣ m,
    from or.inl h,
  right,
  suffices : coprime p m,
    apply coe_coe_dvd.mpr,
    cases bezouts_lemma_coprime this with x hx,
    cases hx with y hxy,
    have hxyn := congr_arg (λ x, ↑n * x) hxy,
    dsimp only [] at hxyn,
    rw [myint.mul_one, myint.mul_add] at hxyn,
    rw ←hxyn,
    apply myint.dvd_sum,
      rw [(by ac_refl : ↑n * (↑p * x) = ↑p * (↑n * x))],
      from myint.dvd_mul (↑n * x) (myint.dvd_refl ↑p),
    rw [←myint.mul_assoc, myint.coe_coe_mul, mul_comm],
    apply myint.dvd_mul,
    apply myint.coe_coe_dvd.mp,
    assumption,
  intros k hkp hkm,
  cases hp.right k hkp with hkeq1 hkeqp,
    from hkeq1,
  rw hkeqp at hkm,
  contradiction,
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
