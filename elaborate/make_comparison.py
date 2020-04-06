"""
Calculate some statistics about Lean files and format into Markdown table.

Very DIY so's to avoid having to think, or think about dependencies
"""

import sys
import pathlib

# robust against calling from another directory
ELABORATE_DIR = pathlib.Path(__file__).parent

# unconventional way to maximise width while obeying PEP8
print("""\
*File*                                    | *Lines* | *Bytes* | *Stripped bytes*
""", end="")
print("""\
:----------------------------------------:| -------:| -------:| ---------------:
""", end="")

def main():
    for stripped_lean_file_path in ELABORATE_DIR.glob("*.stripped.lean"):
        lean_file_path = ELABORATE_DIR / (
                            "{}.lean".format(stripped_lean_file_path.name
                                             [:-len(".stripped.lean")]))
        with lean_file_path.open("r") as lean_file:
            lean_file_lines = list(lean_file)
        with stripped_lean_file_path.open("r") as stripped_lean_file:
            stripped_lean_file_text = stripped_lean_file.read()
        line_count = len(lean_file_lines)
        byte_count = sum(map(len, lean_file_lines))
        stripped_byte_count = len(stripped_lean_file_text)
        print("{:^41} | {:>7} | {:>7} | {:>15}"
                .format("`{}`".format(lean_file_path.name[:-len(".lean")]),
                        line_count,
                        byte_count,
                        stripped_byte_count))

if __name__ == "__main__":
    main()
