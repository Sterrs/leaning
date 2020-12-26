import .ideal

namespace hidden

namespace myring

-- at some point this could be done as a very general construction
-- of quotient groups, I suppose.

variables {α : Type} [myring α]

-- not exactly sure what the most principled type-classical approach is
-- because really we do want to be explicit about which ideal we're
-- quotienting by

def setoid_from_ideal {I: myset α} (hIi: is_ideal I): setoid α :=
setoid.mk (λ a b, a - b ∈ I)
  begin
    split, {
      intro a,
      change a + -a ∈ I,
      rw add_neg,
      from hIi.contains_zero,
    }, split, {
      intros a b,
      assume habI,
      have := hIi.neg_closure _ habI,
      change -(a + -b) ∈ I at this,
      rw neg_distr at this,
      rw add_comm at this,
      rw neg_neg at this,
      from this,
    }, {
      intros a b c,
      assume habI hbcI,
      have := hIi.add_closure _ _ habI hbcI,
      change a + -b + (b + -c) ∈ I at this,
      rw add_assoc at this,
      rw ←add_assoc (-b) at this,
      rw neg_add at this,
      rw zero_add at this,
      from this,
    },
  end

def q_ideal {I: myset α} (hIi: is_ideal I) :=
quotient (setoid_from_ideal hIi)

private def quotient_ring_add
{I: myset α} (hIi: is_ideal I):
q_ideal hIi → q_ideal hIi → q_ideal hIi :=
@quotient.lift₂
  _ _ (q_ideal hIi) (setoid_from_ideal hIi) (setoid_from_ideal hIi)
  (λ a b, @quotient.mk α (setoid_from_ideal hIi) (a + b))
  begin
    intros a b a' b',
    assume haa' hbb',
    change a - a' ∈ I at haa',
    change b - b' ∈ I at hbb',
    have := hIi.add_closure _ _ haa' hbb',
    apply quotient.sound,
    change a + -a' + (b + -b') ∈ I at this,
    rw add_assoc at this,
    rw add_comm (-a') at this,
    rw add_assoc at this,
    rw ←add_assoc a at this,
    rw add_comm (-b') at this,
    rw ←neg_distr at this,
    from this,
  end

private def quotient_ring_mul
{I: myset α} (hIi: is_ideal I):
q_ideal hIi → q_ideal hIi → q_ideal hIi :=
@quotient.lift₂
  _ _ (q_ideal hIi) (setoid_from_ideal hIi) (setoid_from_ideal hIi)
  (λ a b, @quotient.mk α (setoid_from_ideal hIi) (a * b))
  begin
    intros a b a' b',
    assume haa' hbb',
    change a - a' ∈ I at haa',
    change b - b' ∈ I at hbb',
    apply quotient.sound,
    have this1 := hIi.mul_closure b (a - a') haa',
    have this2 := hIi.mul_closure a' (b - b') hbb',
    have := hIi.add_closure _ _ this1 this2,
    change b * (a + -a') + a' * (b + -b') ∈ I at this,
    repeat {rw mul_add at this},
    repeat {rw mul_neg at this},
    rw add_assoc at this,
    rw ←add_assoc (-(b * a')) at this,
    rw mul_comm b a' at this,
    rw neg_add at this,
    rw zero_add at this,
    rw mul_comm b a at this,
    from this,
  end

private def quotient_ring_neg
{I: myset α} (hIi: is_ideal I):
q_ideal hIi → q_ideal hIi :=
@quotient.lift
  _ (q_ideal hIi) (setoid_from_ideal hIi)
  (λ a, @quotient.mk α (setoid_from_ideal hIi) (-a))
  begin
    intros a a',
    assume haa',
    change a - a' ∈ I at haa',
    apply quotient.sound,
    have := hIi.neg_closure _ haa',
    change -(a + -a') ∈ I at this,
    rw neg_distr at this,
    from this,
  end

-- shrug
instance quotient_ring_has_zero
{I: myset α} [hIi: is_ideal I]:
has_zero (q_ideal hIi) :=
⟨@quotient.mk α (setoid_from_ideal hIi) 0⟩

instance quotient_ring_has_one
{I: myset α} [hIi: is_ideal I]:
has_one (q_ideal hIi) :=
⟨@quotient.mk α (setoid_from_ideal hIi) 1⟩

instance quotient_ring_has_add
{I: myset α} [hIi: is_ideal I]:
has_add (q_ideal hIi) :=
⟨quotient_ring_add hIi⟩

instance quotient_ring_has_mul
{I: myset α} [hIi: is_ideal I]:
has_mul (q_ideal hIi) :=
⟨quotient_ring_mul hIi⟩

instance quotient_ring_has_neg
{I: myset α} [hIi: is_ideal I]:
has_neg (q_ideal hIi) :=
⟨quotient_ring_neg hIi⟩

-- can't quite figure out how to make congr work here without
-- spelling out what needs to happen with change anyway.
-- nor can I figure out how to make lean infer the setoid we're
-- working in
instance quotient_ring_is_ring
{I: myset α} [hIi: is_ideal I]:
myring (q_ideal hIi) :=
begin
  split, {
    intros a b c,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) a with x hx, subst hx,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) b with y hy, subst hy,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) c with z hz, subst hz,
    change
        @quotient.mk α (setoid_from_ideal hIi) (x + y + z) =
        @quotient.mk α (setoid_from_ideal hIi) (x + (y + z)),
    rw add_assoc,
  }, {
    intro a,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) a with x hx, subst hx,
    change
        @quotient.mk α (setoid_from_ideal hIi) (x + 0) =
        @quotient.mk α (setoid_from_ideal hIi) x,
    rw add_zero,
  }, {
    intro a,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) a with x hx, subst hx,
    change
        @quotient.mk α (setoid_from_ideal hIi) (x + -x) =
        @quotient.mk α (setoid_from_ideal hIi) 0,
    rw add_neg,
  }, {
    intros a b c,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) a with x hx, subst hx,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) b with y hy, subst hy,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) c with z hz, subst hz,
    change
        @quotient.mk α (setoid_from_ideal hIi) (x * y * z) =
        @quotient.mk α (setoid_from_ideal hIi) (x * (y * z)),
    rw mul_assoc,
  }, {
    intros a b,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) a with x hx, subst hx,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) b with y hy, subst hy,
    change
        @quotient.mk α (setoid_from_ideal hIi) (x * y) =
        @quotient.mk α (setoid_from_ideal hIi) (y * x),
    rw mul_comm,
  }, {
    intro a,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) a with x hx, subst hx,
    change
        @quotient.mk α (setoid_from_ideal hIi) (x * 1) =
        @quotient.mk α (setoid_from_ideal hIi) x,
    rw mul_one,
  }, {
    intros a b c,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) a with x hx, subst hx,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) b with y hy, subst hy,
    cases @quotient.exists_rep _ (setoid_from_ideal hIi) c with z hz, subst hz,
    change
        @quotient.mk α (setoid_from_ideal hIi) (x * (y + z)) =
        @quotient.mk α (setoid_from_ideal hIi) (x * y + x * z),
    rw mul_add,
  },
end

end myring
end hidden