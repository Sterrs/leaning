-- https://www.youtube.com/watch?v=9Efsz2hIpxE
-- deriving some results of the theory of fields, in Lean.

namespace hidden

class myfield (α : Type)
extends has_mul α, has_inv α, has_add α, has_neg α, has_zero α, has_one α :=
-- this axiom can be deduced, so we prove it as a theorem, near the
-- end.
-- (A1 (a b: α): a + b = b + a)
(A2 (a b c: α): a + (b + c) =  (a + b) + c)
(A3 (a: α): a + 0 = a)
(A4 (a: α): a + (-a) = 0)
(M1 (a b: α): a * b = b * a)
(M2 (a b c: α): a * (b * c) = (a * b) * c)
(M3 (a: α): a * 1 = a)
(M4 (a: α): a ≠ 0 → a * (a⁻¹) = 1)
(D (a b c: α): a * (b + c) = a * b + a * c)
(Z: (0: α) ≠ 1)

namespace myfield

variables {α: Type} [myfield α]

variables (a b c x y: α)

-- "Axiom" A1 is proved as Theorem A1.
-- Problems 1-12 are labelled as "theorem p_".
-- There are also some lemmas.
-- This somewhat obscure naming scheme is used for compatibility with the video.

lemma Z': (1: α) ≠ 0 :=
begin
  from (λ h, Z h.symm),
end

lemma l1: a + b = 0 → b + a = 0 :=
begin
  assume h,
  rw ←A4 b,
  conv {
    to_rhs,
    congr,
    rw ←A3 b,
    rw ←h,
  },
  rw ←A2 b (a + b) (-b),
  rw ←A2 a b (-b),
  rw A4 b,
  rw A3 a,
end

lemma l2: (-a) + a = 0 :=
begin
  rw l1 a (-a) (A4 a),
end

lemma l3: 0 + a = a :=
begin
  rw ←A4 a,
  rw ←A2 a (-a) a,
  rw l2 a,
  rw A3 a,
end

lemma l4: a + b = 0 → a + c = 0 → b = c :=
begin
  assume hab hac,
  rw ←l3 c,
  rw ←l1 a b hab,
  rw ←A2 b a c,
  rw hac,
  rw A3 b,
end

lemma l5: a + b = a → b = 0 :=
begin
  assume haba,
  rw ←l2 a,
  conv {
    to_rhs,
    congr, skip,
    rw ←haba,
  },
  rw A2 (-a) a b,
  rw l2 a,
  rw l3 b,
end

lemma l6: (∃ a: α, a + x = a) → x = 0 :=
begin
  assume h,
  cases h with a ha,
  rw ←l3 x,
  rw ←l2 a,
  rw ←A2 (-a) a x,
  rw ha,
end

lemma l7: -(a + b) = -b + (-a) :=
begin
  apply l4 (a + b) (-(a + b)) (-b + -a) (A4 (a + b)),
  rw ←A2 a b (-b + -a),
  rw A2 b (-b) (-a),
  rw A4 b,
  rw l3 (-a),
  rw A4 a,
end

lemma l8: (∃ a, a ≠ 0 ∧ a * x = a) → x = 1 :=
begin
  assume h,
  cases h with a ha,
  rw ←M4 a ha.left,
  conv {
    to_rhs,
    congr,
    rw ←ha.right,
  },
  rw M1 a x,
  rw ←M2 x a (a⁻¹),
  rw M4 a ha.left,
  rw M3 x,
end

theorem p1: a + x = a + y → x = y :=
begin
  assume haxay,
  rw ←l3 x,
  rw ←l2 a,
  rw ←A2 (-a) a x,
  rw haxay,
  rw A2 (-a) a y,
  rw l2 a,
  rw l3 y,
end

theorem p2: a * 0 = 0 :=
begin
  apply p1 (a * 0),
  rw ←D a 0 0,
  rw A3 (0: α),
  rw A3 (a * 0),
end

lemma l9: (-1) * a = -a :=
begin
  apply l4 a ((-1) * a) (-a) _ (A4 a),
  conv {
    to_lhs,
    congr,
    rw ←M3 a,
  },
  rw ←M1 a,
  rw ←D a 1 (-1),
  rw A4 (1: α),
  rw p2 a,
end

lemma l10: a ≠ 0 → a⁻¹ * a = 1 :=
begin
  assume han0,
  rw M1 (a⁻¹) a,
  rw M4 a han0,
end

lemma l11: 1 * a = a :=
begin
  rw M1 1 a,
  rw M3 a,
end

-- hypothesis is much stronger than we need, since we know α is
-- inhabited.
theorem p3: (∀ a: α, a + x = a) → x = 0 :=
begin
  assume h,
  from l6 x ⟨0, h 0⟩,
end

theorem p4: -(0: α) = 0 :=
begin
  from l4 (0: α) (-0) 0 (A4 0) (A3 0),
end

theorem p5: -(-a) = a :=
begin
  from l4 (-a) (- -a) a (A4 (-a)) (l2 a),
end

theorem p6: -(a + b) = -a + (-b) :=
begin
  rw ←l9 (a + b),
  rw D (-1) a b,
  rw l9 a,
  rw l9 b,
end

theorem A1: a + b = b + a :=
begin
  rw ←p5 a,
  rw ←p5 b,
  rw ←p6 (-a) (-b),
  rw ←l7 (-a) (-b),
end

theorem p7: (∀ a, a ≠ 0 → a * x = a) → x = 1 :=
begin
  assume h,
  from l8 x ⟨1, ⟨Z', h 1 Z'⟩⟩,
end

theorem p8: a ≠ 0 → a * x = a * y → x = y :=
begin
  assume han0 haxay,
  rw ←l11 x,
  rw ←l10 a han0,
  rw ←M2 (a⁻¹) a x,
  rw haxay,
  rw M2 (a⁻¹) a y,
  rw l10 a han0,
  rw l11 y,
end

lemma l12: a ≠ 0 → a⁻¹ ≠ 0 :=
begin
  assume han0,
  assume hai0,
  apply @Z α _,
  rw ←M4 a han0,
  rw hai0,
  rw p2 a,
end

theorem p9: a ≠ 0 → (a⁻¹)⁻¹ = a :=
begin
  assume han0,
  conv {
    to_lhs,
    rw ←M3 (a⁻¹⁻¹),
    rw ←l10 a han0,
    rw M2 (a⁻¹⁻¹) (a⁻¹) a,
    rw l10 (a⁻¹) (l12 a han0),
  },
  rw l11 a,
end

theorem p10: (a + b) * c = a * c + b * c :=
begin
  rw M1 (a + b) c,
  rw D,
  rw M1 c a,
  rw M1 c b,
end

theorem p11: a * (-b) = -(a * b) :=
begin
  rw ←l9 b,
  rw ←l9 (a * b),
  rw M2 a (-1) b,
  rw M1 a (-1),
  rw ←M2 (-1) a b,
end

theorem p12: (-1: α) * (-1) = 1 :=
begin
  rw p11 (-1: α) 1,
  rw M1 (-1: α) 1,
  rw p11 (1: α) 1,
  rw p5 (1 * 1: α),
  rw M3 (1: α),
end

end myfield

end hidden
