# Reusable OCaml *plugin* extraction for a pipit2 subpackage.
#
# A package opts in by setting FSTAR_EXTRACT_MODULES (comma-separated F* module
# names it OWNS) and including this file AFTER make/include/base.mk. It then
# gets an `extract` target that emits `--codegen Plugin` OCaml for exactly those
# modules into the shared dune sink $(OCAML_DIR), reusing the package's own
# includes and cache so dependencies resolve exactly as during verification.
#
# Why per-package: each package's module list lives next to the dependencies it
# already declares (FSTAR_INC_DIRS / deps.mk), so extraction captures deps for
# free and a new package self-declares what it contributes. The `plugin`
# package only aggregates the emitted .ml (its dune `(include_subdirs
# unqualified)`) and adds the handwritten registration stub. Every custom module
# must be extracted by exactly one package; F*'s library modules come from
# fstar.lib and are not re-extracted.

OCAML_DIR     ?= $(PIPIT_DIR)/plugin/generated
EXTRACT_STAMP ?= $(CACHE_DIR)/$(COMPONENT).extract

extract: $(EXTRACT_STAMP)
.PHONY: extract

# Re-extract only when this package's checked files change.
$(EXTRACT_STAMP): $(ALL_CHECKED_FILES)
	@echo "[$(COMPONENT)] Extracting [$(FSTAR_EXTRACT_MODULES)] -> $(OCAML_DIR)"
	@mkdir -p $(OCAML_DIR)
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) --ext fly_deps=false \
	  --codegen Plugin --extract $(FSTAR_EXTRACT_MODULES) \
	  --odir $(OCAML_DIR) $(FSTAR_ALL_SRCS)
	@touch $@
