import .lt

open tactic
open tactic.interactive
open interactive (parse)
open interactive.types (texpr)
open lean.parser

-- Convert a goal relating two variables into two goals
-- One showing symmetry of the goal,
-- One with hypothesis m ≤ n showing the original goal.
-- NOTE: If you don't call it `tactic.interactive.` then
-- it doesn't accept arguments.
meta def tactic.interactive.wlog_le
-- Two compulsory arguments want mynat so can get m ≤ n
(m n : parse ident)
-- Two optional arguments to name the hypothesis
(hsymm : parse (optional (tk "with" *> ident)))
(hle : parse (optional ident)): tactic unit :=
do
  -- Load the names m and n into exprs em and en
  em ← get_local m,
  en ← get_local n,
  -- Get two unused names similar to hsymm and hle
  symm_name ← get_unused_name `hsymm,
  le_name ← get_unused_name `hle,
  -- And use them or whatever the tactic was provided with as
  -- optional arguments
  let symm := hsymm.get_or_else symm_name,
  let le := hle.get_or_else le_name,
  -- Revert m and n so we can apply wlogle
  revert_lst [en, em],
  -- Apply wlogle
  tactic.applyc ``hidden.wlogle,
  -- Put everything back into context
  tactic.intro_lst [m, n, symm],
  swap,
  tactic.intro_lst [m, n, le],
  swap

namespace hidden

variables {m n k : mynat}

-- Works excellently
theorem lem_nat_eq2: m = n ∨ m ≠ n :=
begin
  -- It makes it look quite a lot nicer imo.
  wlog_le m n, -- O.o
  {
    cases hsymm with hnm hnnm, {
      left, from hnm.symm,
    }, {
      right,
      assume hnm,
      from hnnm hnm.symm,
    },
  }, {
    cases hle with d hd,
    cases d, {
      simp [hd],
    }, {
      right,
      rw hd,
      assume hmn,
      from succ_ne_zero _ (add_cancel_to_zero _ _ hmn.symm),
    },
  },
end

-- This one fails :(
theorem mul_cancel2: m ≠ 0 → m * n = m * k → n = k :=
begin
  assume hmnz,
  -- It fails for the same reason apply fails if we don't provide
  -- it with p in the original proof.
  -- The tactic needs to turn the reverted ∀ into a λ
  wlog_le k n with hs hl,
  -- revert n k,
  -- apply wlogle (λ n k, m * n = m * k → n = k), {
  --   intros n k,
  --   assume h hmkmn,
  --   from (h hmkmn.symm).symm,
  -- }, {
  --   intros n k,
  --   assume hnk hmnmk,
  --   cases hnk with d hd,
  --   rw [hd, mul_add] at hmnmk,
  --   have hdz' := add_cancel_to_zero _ _ hmnmk,
  --   have hdz := mul_integral _ _ hmnz hdz',
  --   simp [hd, hdz],
  -- },
end

end hidden
