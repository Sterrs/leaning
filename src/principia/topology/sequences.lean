import ..mynat.max
import .continuity
import ..sequence

namespace hidden

namespace topological_space

variables {α β γ: Type}

open classical

local attribute [instance] classical.prop_decidable

def converges_to
(X: topological_space α) (x: α)
(xn: sequence α): Prop :=
∀ U: myset α, X.is_open U → x ∈ U →
∃ N: mynat, ∀ n: mynat, N ≤ n → xn n ∈ U

theorem eventually_constant_converges
(X: topological_space α)
(xn: sequence α)
(x: α):
(∃ (N: mynat), ∀ n: mynat, N ≤ n → xn n = x) →
converges_to X x xn :=
begin
  assume hconst,
  intro U,
  assume hUo,
  assume hxU,
  cases hconst with N hN,
  existsi N,
  intro n,
  assume hNn,
  rw hN n hNn,
  assumption,
end

theorem subsequence_converges
(X: topological_space α) (x: α)
(xn: sequence α) (k_n: mynat → mynat)
(hk_incr: sequence.is_increasing k_n):
X.converges_to x xn → X.converges_to x (sequence.subsequence xn k_n hk_incr) :=
begin
  assume hxnconv,
  intro U,
  assume hUo hxU,
  cases hxnconv U hUo hxU with N hN,
  existsi N,
  intro n,
  assume hNn,
  apply hN,
  apply sequence.subsequence_eventual_growth; assumption,
end

theorem image_converges
(X: topological_space α) (Y: topological_space β)
(x: α) (xn: sequence α) (hxnconv: converges_to X x xn)
(f: α → β) (hfc: is_continuous X Y f):
converges_to Y (f x) (λ n, f (xn n)) :=
begin
  intro U,
  assume hUo hfxU,
  cases hxnconv (myset.inverse_image f U) (hfc U hUo) hfxU with N hN,
  existsi N,
  intro n,
  assume hNn,
  from hN n hNn,
end

theorem hausdorff_limit_unique
(X: topological_space α) (h_ausdorff: is_hausdorff X)
(x: α) (xn: sequence α) (hxnconv: converges_to X x xn)
(y: α) (hynconv: converges_to X y xn):
x = y :=
begin
  by_contradiction hxy,
  have := h_ausdorff _ _ hxy,
  cases this with U this,
  cases this with V hUV,
  cases hxnconv U hUV.open_left hUV.contains_left with N hxN,
  cases hynconv V hUV.open_right hUV.contains_right with M hxM,
  let K := mynat.max M N,
  have := hUV.disjoint,
  rw ←myset.empty_iff_eq_empty at this,
  apply this (xn K),
  split, {
    apply hxN,
    from mynat.max_le_right,
  }, {
    apply hxM,
    from mynat.max_le_left,
  },
end

theorem closed_limit
(X: topological_space α) (Y: myset α)
(hYc: X.is_closed Y)
(x: α) (xn: sequence α) (hxnconv: converges_to X x xn)
(hxnY: ∀ n: mynat, xn n ∈ Y):
x ∈ Y :=
begin
  by_contradiction hxY,
  cases hxnconv (myset.compl Y) hYc hxY with N hN,
  have hxNY := hxnY N,
  have hxNYc := hN N mynat.le_refl,
  contradiction,
end

theorem indiscrete_converges
(x: α) (xn: sequence α):
converges_to (indiscrete_topology α) x xn :=
begin
  intro U,
  assume hUo,
  assume hxU,
  existsi (0: mynat),
  intro n,
  assume h0n,
  cases hUo with h h, {
    rw h at hxU,
    exfalso, from hxU,
  }, {
    rw h,
    trivial,
  },
end

theorem discrete_converges
(x: α) (xn: sequence α):
converges_to (discrete_topology α) x xn ↔
 ∃ N: mynat, ∀ n: mynat, N ≤ n → xn n = x :=
begin
  split, {
    assume hconv,
    cases hconv ({y | y = x}) trivial rfl with N hN,
    existsi N,
    intro n,
    assume hNn,
    from hN n hNn,
  }, {
    apply eventually_constant_converges,
  },
end

theorem product_converges
(X: topological_space α) (Y: topological_space β)
(x: α × β) (xn: sequence (α × β)):
converges_to (product_topology X Y) x xn ↔
(converges_to X x.fst (λ n, (xn n).fst) ∧
 converges_to Y x.snd (λ n, (xn n).snd)) :=
begin
  split, {
    assume hconv,
    split, {
      apply image_converges (product_topology X Y) X x, {
        apply hconv,
      }, {
        apply projection_continuous,
      },
    }, {
      apply image_converges (product_topology X Y) Y x, {
        apply hconv,
      }, {
        apply projection_2_continuous,
      },
    },
  }, {
    assume hconv,
    intro U,
    assume hUo hxU,
    cases hconv with hconvX hconvY,
    cases hUo _ hxU with W hW,
    cases hW.left with W1 hW1,
    cases hW1 with W2 hW12,
    have hxW := hW.right.left,
    rw hW12.eq at hxW,
    cases hconvX W1 hW12.open_left hxW.left with N1 hN1,
    cases hconvY W2 hW12.open_right hxW.right with N2 hN2,
    existsi (mynat.max N1 N2),
    intro n,
    assume hmxn,
    apply hW.right.right,
    rw hW12.eq,
    split, {
      apply hN1,
      transitivity (mynat.max N1 N2), {
        from mynat.max_le_left,
      }, {
        assumption,
      },
    }, {
      apply hN2,
      transitivity (mynat.max N1 N2), {
        from mynat.max_le_right,
      }, {
        assumption,
      },
    },
  },
end

end topological_space

end hidden