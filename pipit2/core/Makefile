ROOT_DIR             ?= ../..
PIPIT_DIR            ?= ..
COMPONENT            ?= pipit2-core
FSTAR_INC_DIRS       ?=
FSTAR_SRC_DIRS       ?= .
FSTAR_ALREADY_CACHED ?=

include ../make/pipit2.mk
include $(ROOT_DIR)/make/include/base.mk

# OCaml plugin extraction: core owns these modules. `make -C core extract`
# emits their `--codegen Plugin` OCaml into the shared plugin dune sink; the
# plugin package then just `dune build`s the aggregate. See ../make/extract.mk.
#
# All of core extracts natively now that the representation is syntactic: the
# old `table` had abstract `ty`/`prim` (erased -> `Obj.t`), so a concrete prim
# match like `step_sofar_and` could not be extracted. With `pterm`/`sterm` as
# plain first-order inductives, even the concrete `Pipit.Example.Bool` rule
# compiles to honest OCaml, so it is back in the extraction set.
FSTAR_EXTRACT_MODULES = Pipit.Exp.Prim,Pipit.Exp.Pure,Pipit.Exp.Source,Pipit.Exp.Anf,Pipit.Source.Stream,Pipit.Transform.Rewrite,Pipit.Example.Bool
include ../make/extract.mk

# base.mk's clean only touches the shared $(BUILD)/cache; also clean the private
# pipit2 cache.
clean::
	@echo "[$(COMPONENT)] Cleaning private cache $(CACHE_DIR)"
	@rm -f $(CACHE_DIR)/*.checked $(CACHE_DIR)/*.extract
