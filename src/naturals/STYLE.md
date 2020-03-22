# Style

Just a rough guide as to what style I'm trying to use

- Near everything to be done in tactic mode
- Two spaces for indent, as was commanded by Sterrrs
- Trailing newlines at end of file
- No trailing whitespace at end of line
- When multiple goals are introduced, wrap each in curly braces `{}`, with
  K&R C convention: the only curly brace to be on its own line should be the
  very last one
- Use fancy tactics like `simp` and `cc` as much as possible.

  However, prefer `refl` over `simp`.
- Always put a trailing comma after the last command in a block, so that you can
  make lean evaluate that command by positioning yourself after the comma.
- Name hypotheses starting with h, except in exceptional circumstances, and then
  follow them with some meaningful initials referring to what the hypothesis is
  about.
- The unary operators `¬`, `←` should *not* be followed by a space.
- The binary operators `+`, `*`, `^`, `∣`, `→`, should be surrounded by a space
  on either side.
- Parenthesise as you see fit.
- In weird ambiguous re-write situations, try to use `conv`.
- Try to keep lines within 80 characters, fairly strictly
- No parentheses after quantifiers
