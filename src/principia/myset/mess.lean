import .basic
import ..mynat.basic

namespace hidden
namespace myset

universes u v w

open myset
open mynat

variables {α : Type u} {β : Type v} {γ : Type w}

def PPP: mynat → Type
| 0        := mynat
| (succ n) := PPP n → Prop

def bigtype: Type :=
(Σ n: mynat, PPP n)

structure bigtype2: Type :=
mk :: (n: mynat) (x: PPP n)

def cartprod2 (I: Type u) (sets: I → Σ α: Type u, myset α): Type (u + 1) :=
{f: I → Σ α: Type u, α //
    ∀ i: I, ∃ hα: (f i).fst = (sets i).fst, (sets i).snd (hα.mp (f i).snd)}

end myset

end hidden
