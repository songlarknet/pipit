BUILD       ?= _build

FSTAR_EXE   ?= fstar.exe
KARAMEL_EXE ?= krml
Z3_EXE 	    ?= z3
Q           ?= @

# Set LAX=1 to disable proofs
LAX ?=
FSTAR_MAYBE_LAX = $(if $(LAX),--lax)

FSTAR_PROOF_OPT   ?=

FSTAR_INC_DIRS = example/ example/ttcan/ \
	pipit/test/ \
	pipit/rts/fstar/ \
	pipit/base/ \
	pipit/core/ pipit/abstract/ pipit/extract/ \
	pipit/source/ \
	pipit/plugin/fst/ pipit/plugin-test/

FSTAR_SRC_DIRS = $(FSTAR_INC_DIRS)


FSTAR_INCLUDES	  ?= $(addprefix --include ,$(FSTAR_INC_DIRS))
FSTAR_CACHE       ?= --cache_dir $(BUILD)/cache --cache_checked_modules --already_cached Prims,FStar,LowStar
FSTAR_HINTS       ?= --hint_dir $(BUILD)/hint --use_hints --record_hints

FSTAR_DEP_OPT     ?= $(FSTAR_INCLUDES) $(FSTAR_CACHE)

FSTAR_EXTRA_OPT   ?=
FSTAR_OPT		  ?= $(FSTAR_INCLUDES) $(FSTAR_PROOF_OPT) $(FSTAR_CACHE) $(FSTAR_EXTRA_OPT) $(FSTAR_MAYBE_LAX) $(FSTAR_HINTS)

FSTAR_SRCS = $(wildcard $(addsuffix *.fst,$(FSTAR_SRC_DIRS)) $(addsuffix *.fsti,$(FSTAR_SRC_DIRS)))


%/deps.mk.rsp:
	@mkdir -p $(shell dirname $@)

.PRECIOUS: %/deps.mk.rsp

# Unfortunately this is pretty slow... it takes 2.5s to update all dependencies, which needs to happen whenever any source file changes.
# They can all be done in parallel though, so it's only 1s with -j8.
%/deps.mk: %/deps.mk.rsp $(FSTAR_SRCS)
	@echo "* Updating dependencies for $@"
	@true $(shell rm -f $@.rsp) $(foreach f,$(FSTAR_SRCS),$(shell echo $(f) >> $@.rsp))
	$(Q) $(FSTAR_EXE) $(FSTAR_DEP_OPT) --dep full @$@.rsp > $@.tmp
	@mv $@.tmp $@

.PHONY: clean
clean:: clean-deps
	@echo "* Cleaning *.checked"
	@rm -f $(BUILD)/cache/*.checked
	@echo "* Cleaning *.extract"
	@rm -f $(BUILD)/*.extract

.PHONY: clean-deps
clean-deps:
	@echo "* Cleaning deps"
	@rm -f $(BUILD)/*/deps.mk
	@rm -f $(BUILD)/*/deps.mk.rsp