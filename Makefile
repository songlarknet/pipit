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
FSTAR_PROOF_OPT   ?= $(FSTAR_NL_DISABLE) $(FSTAR_ARITH_UNBOX)

FSTAR_INCLUDES	  ?= --include src --include example
FSTAR_CACHE       ?= --cache_dir $(BUILD)/cache --cache_checked_modules
FSTAR_HINTS       ?= --hint_dir $(BUILD)/hint --use_hints --record_hints --warn_error -333

# Ignore warning about standard library already being checked...
FSTAR_DEP_OPT     ?= $(FSTAR_INCLUDES) $(FSTAR_CACHE) --warn_error -321

FSTAR_EXTRA_OPT   ?=
FSTAR_OPT		  ?= $(FSTAR_INCLUDES) $(FSTAR_PROOF_OPT) $(FSTAR_CACHE) $(FSTAR_EXTRA_OPT) $(FSTAR_MAYBE_ADMIT)

FSTAR_SRCS = $(wildcard src/**.fst src/**.fsti example/**.fst exampke/**.fsti)

.PHONY: all
all: verify extract

$(BUILD)/deps.mk: $(FSTAR_SRCS)
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

.PHONY: extract
extract: extract-pump

.PHONY: extract-pump
extract-pump: EXTRACT_MODULE=Pump.Extract
extract-pump: EXTRACT_FILE=example/Pump.Extract.fst
extract-pump: EXTRACT_NAME=pump
extract-pump: extract-mk
# extract-pump: $(BUILD)/cache/Example.Compile.Pump.fst.checked extract-mk EXTRACT_MODULE=example/Pump.Extract.fst EXTRACT_NAME=pump

.PHONY: extract-mk
extract-mk:
	@mkdir -p $(BUILD)/extract/$(EXTRACT_NAME)
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $(EXTRACT_FILE) --extract $(EXTRACT_MODULE) --codegen krml --odir $(BUILD)/extract/$(EXTRACT_NAME)
	$(Q)cd $(BUILD)/extract/$(EXTRACT_NAME) && $(KARAMEL_EXE) *.krml -skip-linking

.PHONY: clean
clean:
	@echo "* Cleaning *.checked"
	@rm -f $(BUILD)/cache/*.checked
