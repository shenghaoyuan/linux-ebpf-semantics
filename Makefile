COQC := coqc
COQMAKEFILE := coq_makefile
COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-extraction,-disj-pattern-notation'

DIRS := src ebpf
COQINCLUDES := $(foreach d,$(DIRS),-R $(d) bpf.$(d))

SRC := Zmore.v tnumZ.v tnumZ_inv.v tnumZ_add_sound.v tnumZ_not_sound.v \
		tnumZ_sub_sound.v tnumZ_shift_sound.v tnumZ_mod_eq.v tnumZ_mul_sound.v \
		tnumZ_udiv_sound.v tnumZ_umod_sound.v tnum.v tnum_proof.v
COQSRC := $(addprefix src/,$(SRC))

BPF := Nondeterminism.v CMemoryModel.v GlobalSem.v ebpfSyntax.v ebpfState.v ebpfDecoder.v ebpfBinSem.v Validation.v Extraction.v
COQBPF := $(addprefix ebpf/,$(BPF))

BPF_FILTERED := $(filter-out Validation.v Extraction.v, $(BPF))
COQBPF_FILTERED := $(addprefix ebpf/,$(BPF_FILTERED))

.PHONY: all clean distclean tnumcode bpfcode

all: _CoqProject CoqMakefile
	@echo "Building project..."
	make -f CoqMakefile

_CoqProject:
	@echo "$(COQINCLUDES)" > $@

CoqMakefile: _CoqProject $(COQBPF) $(COQSRC) $(COQBCV)
	@echo "Generating build system..."
	$(COQMAKEFILE) -f $< $(COQBPF) $(COQSRC) $(COQBCV) $(COQEXTRAFLAGS) -o $@

clean:
	@echo "Cleaning build artifacts..."
	@if [ -f CoqMakefile ]; then make -f CoqMakefile clean; fi
	@rm -f _CoqProject CoqMakefile CoqMakefile.conf
	@find . \( \
		-name "*.vo" -o \
		-name "*.vok" -o \
		-name "*.vos" -o \
		-name "*.glob" -o \
		-name "*.aux" -o \
		-name "*.cmi" -o \
		-name "*.cmx" -o \
		-name "*.crashcoqide" \
	\) -exec rm -f {} +
	@rm -f ebpf/validation.ml ebpf/validation.mli

bpfcode:
	coqwc $(COQBPF_FILTERED)

tnumcode:
	coqwc $(COQSRC)

distclean: clean
	@echo "Removing build system files..."
	@rm -f _CoqProject CoqMakefile CoqMakefile.conf