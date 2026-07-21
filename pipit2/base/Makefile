ROOT_DIR             ?= ../..
PIPIT_DIR            ?= ..
COMPONENT            ?= pipit2-base
FSTAR_INC_DIRS       ?=
FSTAR_SRC_DIRS       ?= .
FSTAR_ALREADY_CACHED ?=

include ../make/pipit2.mk
include $(ROOT_DIR)/make/include/base.mk

clean::
	@echo "[$(COMPONENT)] Cleaning private cache $(CACHE_DIR)"
	@rm -f $(CACHE_DIR)/*.checked $(CACHE_DIR)/*.extract
