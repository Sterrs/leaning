-- vim: ts=2 sw=0 sts=-1 et ai tw=70

open tactic
open tactic.interactive
open interactive (parse)
open interactive.types (texpr)
open lean.parser

-- Convert a goal ∀ a b : t, p a b
-- To a λ expr of form λ a b : t, p a b
-- Fails if current goal has incorrect form
meta def goal_to_lambda2 : tactic expr :=
do
  expr.pi a _ ta (expr.pi b _ tb p) ← target,
  return
    (expr.lam a binder_info.default ta
      (expr.lam b binder_info.default tb p))
