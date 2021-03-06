# Style

Just a rough guide as to what style we're trying to use

- Near everything to be done in tactic mode
- Two spaces for indent, as was commanded by Sterrrs
- Trailing newlines at end of file
- No trailing whitespace at end of line
- When multiple goals are introduced, wrap each in curly braces `{}`, with
  K&R C convention: the only curly brace to be on its own line should be the
  very last one
- Use semantic tactics like `contradiction` and `assumption` and fancy tactics
  like `cc` as much as possible.

  However, prefer `refl` over `simp`, and `assumption` over `cc`.

  It is also fine (and perhaps encouraged) to replace invocations of `simp` with
  `rw` at your discretion, as these are likely faster, can make proofs more legible and explicit, don't require Lean to do
  a search every time you load the file, and prevents weird `simp`
  behaviour from breaking existing proofs.
- Try not to use `simp` unless it closes a goal (with an obvious
  exception being `simp at h` followed by `assumption` or
  `contradiction`). This makes it less likely that we will have to
  rewrite the entire proof if a `simp` lemma gets removed or `simp`
  behaviour changes.
- Always put a trailing comma after the last command in a block, so that you can
  make lean evaluate that command by positioning yourself after the comma.
- Name hypotheses starting with h, except in exceptional circumstances, and then
  follow them with some meaningful initials referring to what the hypothesis is
  about.
- Always name hypotheses explicitly (for example use `with` after cases or induction),
  even if choosing to use the generated name.
- Name new constructions with [`my`](https://www.youtube.com/watch?v=H4BNbHBcnDI) as a prefix if you
  feel like it, to emphasise that it is in fact [mine](https://www.youtube.com/watch?v=2dTh3iI0is8)
- The unary operators `¬`, `←` should *not* be followed by a space.
- The binary operators `+`, `*`, `^`, `∣`, `→`, should be surrounded by a space
- For colons, usually put no space before and one space after
  on either side.
- Parenthesise as you see fit.
- In weird ambiguous re-write situations, first, try to use rewrite but specify
  explicit arguments to clear up the ambiguity, if you don't want to write out
  the whole term, only write out the distinguishing part and put `_` where you
  want lean to fill in the gap. As a last resort, use `conv`.
- Try to keep lines within 70 characters. We'd like lines to not wrap in
  VScode basically
- No parentheses after quantifiers
- Put imports on separate lines, as per PEP8 `:)`
- Try to line up the assignments in by-cases definitions
- Leave an empty line between most theorems
- When doing consecutive rewrites, use the `rw [...]` notation.
- If you find yourself doing one rewrite repeatedly, use
  `repeat {rw ...}`.
- If a theorem holds both ways, it's probably worth making it
  an if and only if, as this allows `rw` to work with it
- Use `intro(s)` to introduce conventional mathematical objects (like numbers
  or lists) and `assume` to introduce hypotheses (instances of propositions).
- Use `dsimp only []` to expand lambda expressions
- If you are using `split` multiple times to split up what looks like a
  non-nested expression, indent as follows:
  ```
      split, {
        ...
      }, split, {
        ...
      }, split, {
        ...
      }, {
        ...
      }
  ```

More general tips/useful things not to forget:

- You can still explicitly supply implicit arguments to a function `f` by
  writing `@f`.
- If you want to revert a variable `x` before you induct on another variable,
  you can write `induction ... generalizing x`.
- If you want to induct on some complicated sub-expression (say `x + y`), you
  can use `induction hxy: x + y`. (Note the `hxy: `).
- The same thing works for cases.
- You can clear hypotheses using the `clear` tactic, which can help to reduce
  clutter.
- When a tactic creates goals, a semicolon can be used to apply
  a follow-up tactic to all goals, e.g. `cases ha; assume hab,`
  might save a use of `assume` for the second goal created by `cases`
- When a proof boils down to `cases` or `induction`, it's probably
  worth using | construction to make it a bit more explicit which cases
  are being covered, and to shorten the proof.
- Use `ac_refl` to resolve goals which are equalities dependent only upon
  commutativity and associativity of operations.
- If h is an equality, try using `subst h` to rewrite everything using
  it and then delete it.
- If you are trying to prove a goal of the form `f a = f b` and you know you can
  prove `a = b`, use `apply congr_arg,`. If it somehow doesn't get the right
  `f`, you can explicitly supply a function to `congr_arg`.

  (If you are trying to prove `f a = g b` and you can prove both
  `f = g` and `a = b` then use `apply congr,`. So `apply congr_arg,` is the same
  as `apply congr rfl,`).
- If you want to force lean to write the goal as a definitional equivalent, you
  can use the tactic `change <new equivalent goal>,`. This can be useful if `rw`
  is being boneheaded.
- When using `change`, you don't have to write out the whole goal, you can put
  `_` for things which lean can deduce. In cases where even this is too
  cumbersome, create an auxilliary theorem called `..._def` to rewrite this
  definitional equality
- If you are doing `rw h at h1 h2 ...,`, you can add "`⊢`" to the list to also
  target the current goal.

## Implicit vs Explicit Arguments

- Use explicit arguments by default. Therefore, when using `variables`, normally
use explicit arguments.
- Use implicit arguments when the theorem is an *implication*, for any argument which appears on *both sides* of the implication.
- Use explicit arguments if the theorem is an `↔` or `=`, which will usually be used
via `rw` (so, definitely if it's an `=`, and based on judgement if it's a `↔`).
This is because `rw` allows you to optionally specify explicit arguments to help it
decide which part(s) of the expression to rewrite.
