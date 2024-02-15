FC ?= gfortran

run: writing
	./writing

writing: writing.f90
	$(FC) -o $@ $<

.PHONY: run
