PLUGIN_DEPS=pipit/plugin/fst/
PLUGIN_OPT=--load_cmxs $(BUILD)/pipit_plugin
FSTAR_EXTRA_OPT:=$(FSTAR_EXTRA_OPT) $(PLUGIN_OPT)
FSTAR_DEP_OPT:=$(FSTAR_DEP_OPT) $(PLUGIN_OPT)

PLUGIN_CMX_BIN=$(BUILD)/pipit_plugin.cmxs

PLUGIN_SRCS=$(wildcard pipit/plugin/* pipit/plugin/fst/*)

# TODO maybe split out F* extraction from ocaml build
# TODO better dep tracking?
# XXX in-place builds are a bit better for development / IDE support
# --build-dir=$(realpath $(BUILD))/plugin
$(PLUGIN_CMX_BIN): $(PLUGIN_SRCS)
	@echo " * Building source-extension plugin"
	$(Q)fstar.exe pipit/plugin/fst/*.fst --codegen Plugin --extract Pipit --odir pipit/plugin/generated --include pipit/base
	# Not sure about following includes - extracted Ocaml causes issues, plus it takes a while
	# --include pipit/core --include pipit/extract --include pipit/source --include pipit/abstract --include pipit/rts/fstar
	$(Q)dune build --root=pipit/plugin
	@cp -f pipit/plugin/_build/default/pipit_plugin.cmxs $@
