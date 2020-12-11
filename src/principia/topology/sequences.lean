import ..mynat.max
import .continuous
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

theorem image_of_sequence
(X: topological_space α) (Y: topological_space β)
(x: α) (xn: sequence α) (hxnconv: converges_to X x xn)
(f: α → β) (hfc: @is_continuous _ _ f X Y):
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
  cases hxnconv U hUV.left hUV.right.right.left with N hxN,
  cases hynconv V hUV.right.left hUV.right.right.right.left with M hxM,
  let K := mynat.max M N,
  rw ←myset.empty_iff_eq_empty at hUV,
  apply hUV.right.right.right.right (xn K),
  split, {
    apply hxN,
    from mynat.max_le_right,
  }, {
    apply hxM,
    from mynat.max_le_left,
  },
end


end topological_space

end hidden