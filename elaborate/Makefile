ALL_STRIPPED_LEAN = $(glob *.stripped.lean)

.PHONY: default

default: comparison.md

%.stripped.lean: %.lean
	python3 strip.py < $< > $@

comparison.md: $(ALL) make_comparison.py
	python3 make_comparison.py > $@
