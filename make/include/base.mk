BUILD       		?= $(ROOT_DIR)/_build
COMPONENT   		?= CALLER_MUST_SET_COMPONENT
FSTAR_INC_DIRS 	?= CALLER_MUST_SET_FSTAR_INC_DIRS
FSTAR_SRC_DIRS 	?= CALLER_MUST_SET_FSTAR_SRC_DIRS
FSTAR_ALREADY_CACHED ?= CALLER_MUST_SET_FSTAR_ALREADY_CACHED

FSTAR_EXE   ?= fstar.exe
KARAMEL_EXE ?= krml
Q           ?= @

# Set LAX=1 to disable proofs
LAX ?=
FSTAR_MAYBE_LAX = $(if $(LAX),--lax)

FSTAR_PROOF_OPT   ?=

FSTAR_ALL_INC_DIRS ?= $(addprefix $(PIPIT_DIR)/,$(FSTAR_INC_DIRS)) $(FSTAR_SRC_DIRS)
# FSTAR_ALL_INC_DIRS ?= $(patsubst %,$(BUILD)/%/cache,$(FSTAR_INC_DIRS)) $(addprefix $(PIPIT_DIR)/,$(FSTAR_INC_DIRS)) $(FSTAR_SRC_DIRS)
FSTAR_INCLUDES	  ?= $(addprefix --include ,$(FSTAR_ALL_INC_DIRS))
FSTAR_CACHE       ?= --cache_dir $(BUILD)/cache --cache_checked_modules --already_cached Prims,FStar,LowStar,$(FSTAR_ALREADY_CACHED)

FSTAR_DEP_OPT     ?= $(FSTAR_INCLUDES) $(FSTAR_CACHE)

FSTAR_EXTRA_OPT   ?=
FSTAR_OPT		  ?= $(FSTAR_INCLUDES) $(FSTAR_PROOF_OPT) $(FSTAR_CACHE) $(FSTAR_EXTRA_OPT) $(FSTAR_MAYBE_LAX) $(FSTAR_HINTS)

FSTAR_SRCS = $(wildcard $(addsuffix /*.fst,$(FSTAR_SRC_DIRS)) $(addsuffix /*.fsti,$(FSTAR_SRC_DIRS)))

all: verify
.PHONY: all


%/deps.mk: $(FSTAR_SRCS)
	@echo "[$(COMPONENT)] Updating dependencies"
	@mkdir -p $(dir $@)
	$(Q) $(FSTAR_EXE) $(FSTAR_DEP_OPT) --dep full $(FSTAR_SRCS) -o $@

include $(BUILD)/$(COMPONENT)/deps.mk

.PHONY: clean
clean:: clean-deps
	@echo "[$(COMPONENT)] Cleaning *.checked"
	@rm -f $(BUILD)/cache/*.checked
	@echo "[$(COMPONENT)] Cleaning *.extract"
	@rm -f $(BUILD)/*.extract

.PHONY: clean-deps
clean-deps:
	@echo "[$(COMPONENT)] Cleaning deps"
	@rm -f $(BUILD)/*/deps.mk

%.fst.checked:
	@echo "[$(COMPONENT)] Checking: $<"
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $<
	@touch -c $@

.PHONY: verify
verify: $(ALL_CHECKED_FILES)
