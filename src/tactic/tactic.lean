open tactic
open tactic.interactive
open interactive (parse)
open lean.parser

variables {p q : Prop}

-- This tactic is like `left`, but only works on ∨
meta def myorleft : tactic unit :=
do
  -- Pattern match with the current goal to get exprs l and r for
  -- the left and right side of the `or`
  `(%%l ∨ %%r) ← target,
  -- Make a metavar (to use, and form the goal) out of the expr l
  g ← mk_meta_var l,
  -- Use it to construct the or
  exact `(@or.inl %%l %%r %%g),
  -- Set the goals
  gs ← get_goals,
  set_goals (g::gs)

example (h : p) : p ∨ q :=
begin
  myorleft,
  from h,
end

-- And similarly for ∧
meta def myandsplit : tactic unit :=
do
  -- Pattern match with and
  `(%%l ∧ %%r) ← target,
  -- Make the two metavars we'll need
  gl ← mk_meta_var l,
  gr ← mk_meta_var r,
  -- Exact it
  exact `(@and.intro %%l %%r %%gl %%gr),
  -- Set the goals
  gs ← get_goals,
  set_goals (gl :: gr :: gs)

example (h : q ∧ p): p ∧ q :=
begin
  myandsplit, {
    from h.right,
  }, {
    from h.left,
  },
end


-- Change the goal to false
meta def myexfalso : tactic unit :=
do
  -- Get the current goal
  g ← target,
  -- Create an expr false
  f ← to_expr ``(false),
  -- Create a metavar for the expression false, so we can make a goal
  gfalse ← mk_meta_var f,
  -- mk_app creates an application of false.elim with args g gfalse
  -- Using exact with `(@false.elim) gave a weird error:
  -- invalid quotation, contains universe metavariable
  -- tactic.exact `(@false.elim %%g %%gfalse)
  -- Then we send this to exact
  mk_app ``false.elim [g, gfalse] >>= tactic.exact,
  -- Get the goals (if we chuck them away it would break more complex proofs)
  gs ← get_goals,
  set_goals (gfalse :: gs)

example (hp : p) (h : p → false): q :=
begin
  myexfalso,
  apply h,
  exact hp,
  -- myexfalso, -- fails
end

open classical
-- Use classical reasoning, to convert goal p ∨ q to just q, but
-- assuming ¬p
-- NOTE: If you don't call it `tactic.interactive.` then
-- it doesn't accept arguments.
meta def tactic.interactive.ornotfirst
(h : parse (optional (tk "with" *> ident))) : tactic unit :=
do
  -- Use pattern matching on the target, to get the exprs l and r
  `(%%l ∨ %%r) ← target,
  -- Use what we're given, call it "this" otherwise
  let hh := h.get_or_else `this,
  -- Do cases on excluded middle, load it into temporary thing called
  -- hp (probably risky if there could be something else called hp
  -- - use mk_fresh_name?) and put the ¬p into hh
  cases `(em %%l) [`hp, hh],
  -- Get the temporary thing we just made, as an expr
  hhp ← to_expr ```(hp),
  -- Use it to form the term we need
  tactic.exact `(@or.inl %%l %%r %%hhp),
  -- Now the user only needs to solve the right
  tactic.right,
  -- Do nothing, necessary to form type tactic unit
  tactic.skip

example (h : ¬p → q): p ∨ q :=
(or.elim (em p)
  (assume hp,
   show p∨q, from or.inl hp)
  (assume hnp,
   show p∨q, from or.inr (h hnp)))

example (h : ¬p → q): p ∨ q :=
begin
  ornotfirst with hnp,
  from h hnp,
end

-- From the tactic writing tutorial : here for reference
open interactive (loc.ns)
open interactive.types (texpr location)
meta def tactic.interactive.mul_left (q : parse texpr) : parse location → tactic unit
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» h ``(%%e*%%l = %%e*%%r) ``(congr_arg (λ x, %%e*x) %%H),
   tactic.clear H
| _ := tactic.fail "mul_left takes exactly one location"

example (a b c : ℤ) (hyp : a = b) : c*a = c*b :=
begin
  mul_left c at hyp,
  exact hyp
end

