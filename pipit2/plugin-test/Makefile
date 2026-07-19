ROOT_DIR             ?= ../..
PIPIT_DIR            ?= ..
COMPONENT            ?= pipit2-plugin-test
FSTAR_INC_DIRS       ?= core plugin/_build/default
FSTAR_SRC_DIRS       ?= .
FSTAR_ALREADY_CACHED ?=

# Load the compiled pipit2 plugin so its `[@@plugin]` definitions (notably
# `Pipit.Exp.Anf.to_anf`) are registered as native normalizer primitive steps.
# With the plugin loaded, an `assert_norm`/`norm` over `to_anf` reduces via the
# extracted OCaml rather than the F* interpreter. `--load_cmxs` fails hard if the
# cmxs is missing, so the top-level Makefile builds `plugin` before this package.
FSTAR_EXTRA_OPT      += --load_cmxs pipit2_plugin

include ../make/pipit2.mk
include $(ROOT_DIR)/make/include/base.mk

clean::
	@echo "[$(COMPONENT)] Cleaning private cache $(CACHE_DIR)"
	@rm -f $(CACHE_DIR)/*.checked $(CACHE_DIR)/*.extract
