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

FSTAR_INCLUDES	  ?= --include src --include example --include example/ttcan
FSTAR_CACHE       ?= --cache_dir $(BUILD)/cache --cache_checked_modules --already_cached Prims,FStar,LowStar
FSTAR_HINTS       ?= --hint_dir $(BUILD)/hint --use_hints --record_hints --warn_error -333

FSTAR_DEP_OPT     ?= $(FSTAR_INCLUDES) $(FSTAR_CACHE)

FSTAR_EXTRA_OPT   ?=
FSTAR_OPT		  ?= $(FSTAR_INCLUDES) $(FSTAR_PROOF_OPT) $(FSTAR_CACHE) $(FSTAR_EXTRA_OPT) $(FSTAR_MAYBE_ADMIT)

FSTAR_SRCS = $(wildcard src/*.fst src/*.fsti src/**/*.fst src/**/*.fsti example/*.fst example/*.fsti example/**/*.fst example/**/*.fsti)

.PHONY: all
all: verify extract

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

# `make lax`:
# Sometimes the proofs are flaky during development, so it can be useful to
# build with retries enabled. 
lax: FSTAR_PROOF_OPT=--retry 2
lax: verify

.PHONY: extract
extract: extract-pump extract-fixed

.PHONY: extract-pump
extract-pump: EXTRACT_MODULE=Pump.Extract
extract-pump: EXTRACT_FILE=example/Pump.Extract.fst
extract-pump: EXTRACT_NAME=pump
extract-pump: extract-mk

.PHONY: extract-fixed
extract-fixed: EXTRACT_MODULE=Explore.FixedSizeArray
extract-fixed: EXTRACT_FILE=example/Explore.FixedSizeArray.fst
extract-fixed: EXTRACT_NAME=fixed
extract-fixed: KRML_OPT=-skip-compilation
extract-fixed: extract-mk


.PHONY: extract-therm-manual
extract-therm-manual: EXTRACT_MODULE=ThermDriver.Manual
extract-therm-manual: EXTRACT_FILE=example/ThermDriver.Manual.fst --extract FStar.UInt8 --extract FStar.Pervasives
extract-therm-manual: EXTRACT_NAME=therm-manual
extract-therm-manual: extract-mk

.PHONY: extract-mk
extract-mk:
	@echo "* Extracting $(EXTRACT_MODULE)"
	@mkdir -p $(BUILD)/extract/$(EXTRACT_NAME)
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $(EXTRACT_FILE) --extract $(EXTRACT_MODULE) --codegen krml --odir $(BUILD)/extract/$(EXTRACT_NAME)
	$(Q)cd $(BUILD)/extract/$(EXTRACT_NAME) && $(KARAMEL_EXE) *.krml -skip-linking $(KRML_OPT)

.PHONY: clean
clean:
	@echo "* Cleaning *.checked"
	@rm -f $(BUILD)/cache/*.checked
