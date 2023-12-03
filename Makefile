# Main targets:
#
# `make dev-init`: set up local opam switch for development
#
# `make all` (default): verify Pipit itself, verify examples, and extract C code for examples
#
# `make verify`
# `make verify-retry`: enable retries on failures (useful for developing with flaky SMT proofs)
#
# `make build/cache/Module.Name.fst.checked`: check specific file
#
# `make extract`: extract C code for examples
# `make extract-pump`, `extract-simple`, `extract-ttcan`
#
# `make clean`
#
BUILD       ?= build

FSTAR_EXE   ?= fstar.exe
KARAMEL_EXE ?= krml
Z3_EXE 	    ?= z3
Q           ?= @

# Set ADMIT=1 to admit queries
ADMIT ?=
FSTAR_MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR_NL_DISABLE  ?= --z3smtopt '(set-option :smt.arith.nl false)'
FSTAR_ARITH_UNBOX ?= --smtencoding.l_arith_repr native --smtencoding.elim_box true
# Disable FSTAR_NL_DISABLE and FSTAR_ARITH_UNBOX: for some reason this breaks the proof of lemma_lift_subst_distribute_le.
FSTAR_PROOF_OPT   ?=

FSTAR_SRC_DIRS = example/ $(wildcard example/*/) src/ $(wildcard src/*/) test/ $(wildcard test/*/) rts/fstar

FSTAR_INCLUDES	  ?= $(addprefix --include ,$(FSTAR_SRC_DIRS))
FSTAR_CACHE       ?= --cache_dir $(BUILD)/cache --cache_checked_modules --already_cached Prims,FStar,LowStar
FSTAR_HINTS       ?= --hint_dir $(BUILD)/hint --use_hints --record_hints --warn_error -333

FSTAR_DEP_OPT     ?= $(FSTAR_INCLUDES) $(FSTAR_CACHE)

FSTAR_EXTRA_OPT   ?=
FSTAR_OPT		  ?= $(FSTAR_INCLUDES) $(FSTAR_PROOF_OPT) $(FSTAR_CACHE) $(FSTAR_EXTRA_OPT) $(FSTAR_MAYBE_ADMIT)

FSTAR_SRCS = $(wildcard $(addsuffix *.fst,$(FSTAR_SRC_DIRS)) $(addsuffix *.fsti,$(FSTAR_SRC_DIRS)))

.PHONY: all
all: verify-retry extract

$(BUILD)/deps.mk.rsp:
	@mkdir -p $(BUILD)

$(BUILD)/deps.mk: $(BUILD)/deps.mk.rsp $(FSTAR_SRCS)
	@echo "* Updating dependencies"
	@true $(shell rm -f $@.rsp) $(foreach f,$(FSTAR_SRCS),$(shell echo $(f) >> $@.rsp))
	$(Q)$(FSTAR_EXE) $(FSTAR_DEP_OPT) --dep full @$@.rsp > $@.tmp
	@mv $@.tmp $@

include $(BUILD)/deps.mk

%.fst.checked:
	@echo "* Checking: $<"
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $<
	@touch -c $@

.PHONY: verify
verify: $(ALL_CHECKED_FILES)

# `make verify-retry`:
# Sometimes the proofs are flaky during development, so it can be useful to
# build with retries enabled.
verify-retry: FSTAR_PROOF_OPT=--retry 2
verify-retry: verify

.PHONY: extract
extract: extract-pump extract-simple

.PHONY: extract-pump
extract-pump: EXTRACT_MODULE=Pump.Extract
extract-pump: EXTRACT_FILE=example/Pump.Extract.fst
extract-pump: EXTRACT_NAME=pump
extract-pump: extract-mk

.PHONY: extract-simple
extract-simple: EXTRACT_MODULE=Simple.Extract
extract-simple: EXTRACT_FILE=example/Simple.Extract.fst
extract-simple: EXTRACT_NAME=simple
extract-simple: extract-mk

# don't build by default yet, wait until stable
.PHONY: extract-ttcan
extract-ttcan: EXTRACT_MODULE=Network.TTCan.Extract
extract-ttcan: EXTRACT_FILE=example/ttcan/Network.TTCan.Extract.fst
extract-ttcan: EXTRACT_NAME=ttcan
extract-ttcan: extract-mk

.PHONY: extract-mk
extract-mk:
	@echo "* Extracting $(EXTRACT_MODULE)"
	@rm -f $(BUILD)/extract/$(EXTRACT_NAME)/*.krml
	@mkdir -p $(BUILD)/extract/$(EXTRACT_NAME)
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $(EXTRACT_FILE) --codegen krml --odir $(BUILD)/extract/$(EXTRACT_NAME)
	$(Q)cd $(BUILD)/extract/$(EXTRACT_NAME) && $(KARAMEL_EXE) *.krml -bundle $(EXTRACT_MODULE)=* -skip-linking -skip-compilation $(KRML_OPT)

.PHONY: clean
clean:
	@echo "* Cleaning *.checked"
	@rm -f $(BUILD)/cache/*.checked
	@echo "* Cleaning deps"
	@rm -f $(BUILD)/deps.mk
	@rm -f $(BUILD)/deps.mk.rsp

.PHONY: dev-init
dev-init:
	@echo "* Setting up development environment"
	@echo "* Checking for Python 2.7"
	@python2.7 -c 'print "Python 2.7 OK"' || (echo 'Cannot find Python 2.7. FStar and Z3 need Python 2.7. See https://github.com/songlarknet/pipit#modern-linux-no-python-27'; exit 1)
	@echo "* Updating opam index"
	@opam update
	@echo "* Create a local opam switch with OCaml 4.14"
	@opam switch create . 4.14.1
	@echo "* Pinning development version of F*"
	@opam pin add fstar --dev-repo --no-action
	@echo "* Pinning development version of karamel; building"
	@opam pin add karamel --dev-repo --yes --no-depexts
# no-depexts is required for Linux without Python 2.7 apt package