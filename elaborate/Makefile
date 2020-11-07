ALL_STRIPPED_LEAN = $(patsubst %.lean, %.stripped.lean, $(filter-out $(wildcard *.stripped.lean), $(wildcard *.lean)))

.PHONY: default

default: comparison.md ../README.md

%.stripped.lean: %.lean
	python3 strip.py < $< > $@

comparison.md: $(ALL_STRIPPED_LEAN) make_comparison.py
	python3 make_comparison.py > $@

# this is now highly unstable
# ../README.md: comparison.md
# 	{ git show lean-3.4.2:README.md && cat $<; } > $@
