import .basic
import ..logic
import ..sequence
import ..mynat.max

namespace hidden
namespace myring

structure polynomial (α : Type) [myring α] :=
(seq : sequence α)
(eventually_zero : ∃ N, ∀ n, N ≤ n → seq n = 0)

namespace polynomial

variables {α : Type} [myring α]

theorem polyext (a b : polynomial α) : (∀ n, a.seq n = b.seq n) → a = b :=
begin
  assume h,
  cases a,
  cases b,
  dsimp at h,
  simp,
  apply funext,
  assumption,
end

def add : polynomial α → polynomial α → polynomial α :=
λ a b, ⟨a.seq + b.seq, begin
  cases a.eventually_zero with N hN,
  cases b.eventually_zero with M hM,
  existsi (mynat.max N M),
  intros n hn,
  change a.seq n + b.seq n = 0,
  suffices h₁ : a.seq n = 0,
    suffices h₂ : b.seq n = 0,
      rw [h₁, h₂, add_zero],
    apply hM,
    apply @mynat.max_le_cancel_right N M n,
    assumption,
  apply hN,
  apply @mynat.max_le_cancel_left N M n,
  assumption,
end⟩

instance: has_add (polynomial α) := ⟨add⟩

instance: has_zero (polynomial α) := ⟨⟨λ n, 0, begin
  existsi (0 : mynat),
  intros n hn,
  refl,
end⟩⟩

def neg : polynomial α → polynomial α :=
λ a, ⟨λ n, -a.seq n, begin
  cases a.eventually_zero with N hN,
  existsi N,
  intros n hn,
  symmetry,
  rw [←neg_unique, zero_add],
  apply hN,
  assumption,
end⟩

instance: has_neg (polynomial α) := ⟨neg⟩

-- Same formula for power series ring
-- term_collection a b m n = a_m b_n + a_{m + 1} b_{n-1} + ... + a_{m + n} b_0
private def term_collection (seq₁ : sequence α) (seq₂ : sequence α) : mynat → mynat → α
| m 0              := seq₁ m * seq₂ 0
| m (mynat.succ n) := seq₁ m * seq₂ (n.succ) + (term_collection m.succ n)

private lemma term_collection_zero (seq₁ seq₂ : sequence α) (m n N : mynat)
(h : ∀ a b, N ≤ a + b → seq₁ a * seq₂ b = 0) :
(N ≤ m + n → term_collection seq₁ seq₂ m n = 0) :=
begin
  assume hmnN,
  -- Holy fuck it took me ages to remember `generalizing`
  induction n with n hn generalizing m, {
    rw mynat.zz at *,
    unfold term_collection,
    apply h,
    assumption,
  }, {
    unfold term_collection,
    rw [h m n.succ hmnN, zero_add],
    rw mynat.add_succ at hmnN,
    apply hn,
    rwa mynat.succ_add,
  },
end

private lemma term_collection_succ (a b : sequence α) (m n : mynat) :
term_collection a b m.succ n = term_collection a b m n.succ + -(a m * b n.succ) := sorry

-- Formula for what happens if you swap a and b.
private lemma term_collection_swap_args_lemma (a b : sequence α) (m n : mynat) :
term_collection b a m.succ n + term_collection a b n.succ m = term_collection a b 0 (m + n).succ :=
begin
  induction n with n hn generalizing m, {
    rw [mynat.zz, mynat.add_zero],
    dsimp only [term_collection],
    rw mul_comm,
  }, {
    rw [mynat.add_succ],
    have := hn m.succ,
    rw mynat.succ_add at this,
    rw this.symm,
    conv {
      congr,
        congr,
          skip,
        rw term_collection_succ,
        skip,
      congr,
        rw term_collection_succ,
        skip,
      skip,
    },
    ac_refl,
  },
end

private theorem term_collection_swap_args (a b : sequence α) (m n : mynat) :
term_collection b a m.succ n = term_collection a b 0 (m + n).succ + -term_collection a b n.succ m :=
begin
  apply add_cancel_right _ _ (term_collection a b n.succ m),
  rw [add_assoc, neg_add, add_zero, term_collection_swap_args_lemma],
end

open classical

-- Move to mynat? Prove in ordered_myring?
-- This is a slightly strange method of proof
private lemma sum_lemma {m n M N : mynat} : M + N ≤ m + n → M ≤ m ∨ N ≤ n :=
begin
  assume h,
  by_cases hm: M ≤ m,
    left, assumption,
  right,
  change m < M at hm,
  by_contradiction hn,
  change n < N at hn,
  rw ←@not_not (M + N ≤ m + n) at h,
  change ¬(m + n < M + N) at h,
  apply h,
  apply mynat.lt_comb; assumption,
end

def mul : polynomial α → polynomial α → polynomial α :=
λ a b, ⟨λ n, term_collection a.seq b.seq 0 n, begin
  cases a.eventually_zero with N hN,
  cases b.eventually_zero with M hM,
  existsi N + M,
  intros n hNMn,
  apply term_collection_zero _ _ _ _ (N + M),
    intros i j hij,
    suffices: N ≤ i ∨ M ≤ j,
      suffices h₁: a.seq i = 0 ∨ b.seq j = 0,
        cases h₁ with h₁a h₁b,
          rw [h₁a, zero_mul],
        rw [h₁b, mul_zero],
      cases this,
        left,
        apply hN,
        assumption,
      right,
      apply hM,
      assumption,
    apply sum_lemma,
    assumption,
  rwa mynat.zero_add,
end⟩

instance: has_mul (polynomial α) := ⟨mul⟩

instance: has_one (polynomial α) := ⟨⟨λ n, if n = 0 then 1 else 0, begin
  existsi (1 : mynat),
  intro n,
  assume h2n,
  change (0 : mynat).succ ≤ n at h2n,
  rw ←mynat.lt_iff_succ_le at h2n,
  apply if_neg,
  assume hn0,
  apply @mynat.lt_impl_neq 0 n,
    assumption,
  symmetry, assumption,
end⟩⟩

variables a b c : polynomial α

private theorem poly_add_assoc : a + b + c = a + (b + c) :=
begin
  apply polyext,
  intro n,
  change a.seq n + b.seq n + c.seq n = a.seq n + (b.seq n + c.seq n),
  rw add_assoc,
end

private theorem poly_add_zero : a + 0 = a :=
begin
  apply polyext,
  intro n,
  change a.seq n + 0 = a.seq n,
  rw add_zero,
end

private theorem poly_add_neg : a + -a = 0 :=
begin
  apply polyext,
  intro n,
  change a.seq n + -(a.seq n) = 0,
  rw add_neg,
end

private theorem poly_mul_assoc : a * b * c = a * (b * c) :=
begin
  sorry,
end

private theorem poly_mul_comm : a * b = b * a :=
begin
  apply polyext,
  intro n,
  change term_collection a.seq b.seq 0 n = term_collection b.seq a.seq 0 n,
  cases n,
    rw mynat.zz,
    dsimp only [term_collection],
    rw mul_comm,
  conv {
    to_lhs,
    dsimp only [term_collection],
    rw [term_collection_swap_args, mynat.zero_add],
    dsimp only [term_collection],
    congr,
      rw mul_comm,
      skip,
    rw add_comm,
  },
  rw [←add_assoc, add_neg, zero_add],
  refl,
end

private theorem poly_mul_one : a * 1 = a :=
begin
  sorry,
end

private theorem poly_mul_add : a * (b + c) = a * b + a * c :=
begin
  apply polyext,
  intro n,
  change term_collection a.seq (b.seq + c.seq) 0 n = (a * b).seq n + (a * c).seq n,
  sorry,
end

instance: myring (polynomial α) :=
⟨poly_add_assoc, poly_add_zero, poly_add_neg,
poly_mul_assoc, poly_mul_comm, poly_mul_one, poly_mul_add⟩

end polynomial

end myring
end hidden
