import .basic
import ..myset.basic

namespace hidden

namespace myring

structure ideal {α : Type} [myring α] (I : myset α) :=
(add_closure (a b : α) : a ∈ I → b ∈ I → a + b ∈ I)
(neg_closure (a : α) : a ∈ I → -a ∈ I)
(mul_closure (r x : α) : x ∈ I → r * x ∈ I)

variables {α : Type} [myring α] (I J : myset α)

def ideal_intersection (iI : ideal I) (iJ : ideal J) : ideal (I ∩ J) := ⟨
begin
  intros a b,
  assume haIJ hbIJ,
  split,
    apply iI.add_closure _ _ haIJ.left hbIJ.left,
  apply iJ.add_closure _ _ haIJ.right hbIJ.right,
end, begin
  intro a,
  assume haIJ,
  split,
    apply iI.neg_closure _ haIJ.left,
  apply iJ.neg_closure _ haIJ.right,
end, begin
  intros r x,
  assume h,
  split,
    apply iI.mul_closure _ _ h.left,
  apply iJ.mul_closure _ _ h.right,
end⟩

variables {β : Type} [myring β]

def ker (f : α → β) : myset α := { a | f a = 0 }
def im (f : α → β) : myset β := { b | ∃ a, f a = b }

structure is_homomorphism (f : α → β) : Prop :=
intro :: -- necessary ?
(respects_add (a b : α) : f (a + b) = f a + f b)
(respects_mul (a b : α) : f (a * b) = f a * f b)
(respects_one (a b : α) : f 1 = 1)

namespace is_homomorphism

variables {f : α → β} (hf : is_homomorphism f)

include hf

theorem respects_zero : f 0 = 0 :=
begin
  apply add_cancel_left (f 0),
  rw [←hf.respects_add, add_zero, add_zero],
end

theorem respects_neg (a : α) : f (-a) = -f a :=
begin
  rw [←neg_unique, ←respects_add hf, neg_add, respects_zero hf],
end

def kernel_ideal : ideal (ker f) := ⟨begin
  intros a b,
  assume ha hb,
  change f (a + b) = 0,
  change f a = 0 at ha,
  change f b = 0 at hb,
  rw [hf.respects_add, ha, hb, add_zero],
end, begin
  intro a,
  assume ha,
  change f (-a) = 0,
  change f a = 0 at ha,
  symmetry,
  rw [hf.respects_neg, ←neg_unique, ha, zero_add],
end, begin
  intros r x,
  assume hx,
  change f (r * x) = 0,
  change f x = 0 at hx,
  rw [hf.respects_mul, hx, mul_zero],
end⟩

end is_homomorphism



end myring

end hidden