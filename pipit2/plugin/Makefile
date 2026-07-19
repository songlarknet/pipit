# pipit2 language plugin.
#
# Deliberately minimal: it extracts the core definitions (`Pipit.Exp.Base`)
# from F* to OCaml with `--codegen Plugin`, and packages them with a tiny bit
# of handwritten OCaml (`Pipit2_Plugin.ml`) that registers the `#lang-pipit`
# extension. For now `#lang-pipit` is a passthrough (it parses as ordinary
# F*); the point is only to (a) prove the extract+dune packaging works and
# (b) make the language name available. Real preprocessing / lifting lands
# later.
#
# This Makefile is intentionally standalone (it does not use base.mk's
# verify/deps machinery): the F* it needs is verified by the `core` subpackage,
# which writes `Pipit.Exp.Base.fst.checked` into the shared pipit2 cache. Build
# order (see ../Makefile) guarantees core runs first.

# pipit2 language plugin.
#
# Deliberately minimal: it aggregates the OCaml that the pipit2 packages emit
# (each package extracts the modules it OWNS with `--codegen Plugin` into the
# shared sink `generated/` -- see ../make/extract.mk) together with a tiny bit
# of handwritten OCaml (`Pipit2_Plugin.ml`) that registers the `#lang-pipit`
# extension. For now `#lang-pipit` is a passthrough (it parses as ordinary
# F*); the point is only to (a) prove the extract+dune packaging works and
# (b) make the language name available. Real preprocessing / lifting lands
# later.
#
# This package does NOT extract anything itself; extraction is owned per-package
# (core, and future packages). The top-level ../Makefile runs the packages'
# `extract` targets before building here, so `generated/` is populated first.

all: plugin
.PHONY: all plugin clean

# Compile the extracted OCaml (generated/*.ml) together with the handwritten
# registration stub. `generated/` is populated by the packages' `extract`
# targets, sequenced ahead of this by ../Makefile.
plugin: Pipit2_Plugin.ml dune dune-project
	@echo "[pipit2-plugin] Building plugin (dune)"
	dune build

clean:
	@echo "[pipit2-plugin] Cleaning"
	@rm -rf _build
