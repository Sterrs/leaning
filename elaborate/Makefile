ALL_STRIPPED_LEAN = $(patsubst %.lean, %.stripped.lean, $(filter-out $(wildcard *.stripped.lean), $(wildcard *.lean)))

.PHONY: default

default: comparison.md

%.stripped.lean: %.lean
	python3 strip.py < $< > $@

comparison.md: $(ALL_STRIPPED_LEAN) make_comparison.py
	python3 make_comparison.py > $@
