import ..existence ..relations.conga ..relations.congs

noncomputable theory

structure triangle : Type :=
{A B C : point}
(hnc : ¬collinear A B C)
notation `▵`:50 := triangle.mk

-- All the definitions you'd expect of a
-- triangle
namespace triangle

variable (t : triangle)

include t

-- There should be an efficient way to do these

theorem neqAB : t.A ≠ t.B := ncoll_imp_neq12 t.hnc
theorem neqAC : t.A ≠ t.C := ncoll_imp_neq13 t.hnc
theorem neqBC : t.B ≠ t.C := ncoll_imp_neq23 t.hnc

def AB : line := line_through t.neqAB
def AC : line := line_through t.neqAC
def BC : line := line_through t.neqBC

def c : segment := t.A↦t.B
def a : segment := t.B↦t.C
def b : segment := t.C↦t.A

def ABC : angle :=
begin
  apply @angle.mk t.AB t.BC,
  existsi t.B,
  split,
    have := on_line_through2 t.neqAB,
    have : t.AB = line_through t.neqAB,
      refl,
    rw this,
    assumption,
  have := on_line_through1 t.neqBC,
  have : t.BC = line_through t.neqBC,
    refl,
  rw this,
  assumption,
end
def CBA : angle := t.ABC.complement
def BCA : angle :=
begin
  have ncollBCA : ¬ collinear t.B t.C t.A :=
  ncoll_symm12 (ncoll_symm13 t.hnc),
  let s := ▵ ncollBCA,
  from s.ABC,
end
def ACB : angle := t.BCA.complement
def CAB : angle :=
begin
  have ncollBCA : ¬ collinear t.C t.A t.B :=
  ncoll_symm13 (ncoll_symm12 t.hnc),
  let s := ▵ ncollBCA,
  from s.ABC,
end
def BAC : angle := t.CAB.complement

end triangle

-- Given three points we can construct the angle between
-- them
theorem corner {A B C : point} (h : ¬collinear A B C) :
∃ α : angle,
(A ⊏ α.ℓ₁) ∧ (B ⊏ α.ℓ₁) ∧ (B ⊏ α.ℓ₂) ∧ (C ⊏ α.ℓ₂) :=
begin
  let t := ▵ h,
  existsi t.ABC,
  split,
    suffices heq : (triangle.ABC t).ℓ₁ = t.AB,
      exact on_line_through1 t.neqAB,
    refl,
  split,
    suffices heq : (triangle.ABC t).ℓ₁ = t.AB,
      exact on_line_through2 t.neqAB,
    refl,
  split,
    suffices heq : (triangle.ABC t).ℓ₂ = t.BC,
      exact on_line_through1 t.neqBC,
    refl,
  suffices heq : (triangle.ABC t).ℓ₂ = t.BC,
    exact on_line_through2 t.neqBC,
  refl,
end

-- One of the last axioms.
-- SAS congruence
def congt (s t : triangle) : Prop :=
s.b ≅ t.b ∧ s.c ≅ t.c ∧ conga s.BAC t.BAC

axiom congt_imp_ang_cong (s t : triangle) :
congt s t → conga s.ABC t.ABC

-- TODO: ASA SSS congruence (difficult)
-- ASS non-congruence
