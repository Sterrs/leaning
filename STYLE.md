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
  `rw` at your discretion, as these are likely faster, and can make proofs more
  legible.
- Always put a trailing comma after the last command in a block, so that you can
  make lean evaluate that command by positioning yourself after the comma.
- Name hypotheses starting with h, except in exceptional circumstances, and then
  follow them with some meaningful initials referring to what the hypothesis is
  about.
- Always name hypotheses explicitly (for example use `with` after cases or induction),
  even if choosing to use the generated name.
- The unary operators `¬`, `←` should *not* be followed by a space.
- The binary operators `+`, `*`, `^`, `∣`, `→`, should be surrounded by a space
- For colons, usually put no space before and one space after
  on either side.
- Parenthesise as you see fit.
- In weird ambiguous re-write situations, try to use `conv`.
- Try to keep lines within 80 characters, fairly strictly
- No parentheses after quantifiers
- Put imports on separate lines, as per PEP8 `:)`
- Try to line up the assignments in by-cases definitions
- Leave an empty line between most theorems