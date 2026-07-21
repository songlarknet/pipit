ROOT_DIR             ?= ../..
PIPIT_DIR            ?= ..
COMPONENT            ?= pipit2-base
FSTAR_INC_DIRS       ?=
FSTAR_SRC_DIRS       ?= .
FSTAR_ALREADY_CACHED ?=

include ../make/pipit2.mk
include $(ROOT_DIR)/make/include/base.mk

# base OWNS the Pipit.Base.* namespace: a single namespace selector extracts
# every module under it, so new base modules are picked up without editing this
# list. (F*'s --extract accepts module *or namespace* selectors.)
FSTAR_EXTRACT_MODULES = Pipit.Base
include ../make/extract.mk

clean::
	@echo "[$(COMPONENT)] Cleaning private cache $(CACHE_DIR)"
	@rm -f $(CACHE_DIR)/*.checked $(CACHE_DIR)/*.extract
