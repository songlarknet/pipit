PLUGIN_DEPS=pipit/plugin/fst/
PLUGIN_OPT=--load_cmxs $(BUILD)/plugin/default/pipit_plugin
FSTAR_EXTRA_OPT:=$(FSTAR_EXTRA_OPT) $(PLUGIN_OPT)
FSTAR_DEP_OPT:=$(FSTAR_DEP_OPT) $(PLUGIN_OPT)

PLUGIN_CMXA=$(BUILD)/plugin/default/pipit_plugin.cmxa

PLUGIN_SRCS=$(wildcard pipit/plugin/* pipit/plugin/fst/*)

# TODO maybe split out F* extraction from ocaml build
# TODO better dep tracking?
$(PLUGIN_CMXA): $(PLUGIN_SRCS)
	@echo " * Building source-extension plugin"
	$(Q)fstar.exe pipit/plugin/fst/*.fst --codegen Plugin --extract Pipit --odir pipit/plugin/generated
	$(Q)dune build --root=pipit/plugin --build-dir=$(realpath $(BUILD))/plugin
	@touch $@
