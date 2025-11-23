ROOT_DIR 				?= ../..
PIPIT_DIR 			?= ..
COMPONENT   		?= plugin
FSTAR_INC_DIRS 	?= base core rts/fstar
# FSTAR_INC_DIRS 	?= base core
FSTAR_SRC_DIRS 	?= fst
FSTAR_ALREADY_CACHED ?=

FSTAR_EXTRACT_MODULES = Pipit.Plugin.Interface,Pipit.Tactics


include $(ROOT_DIR)/make/include/base.mk

# TODO
all: plugin
.PHONY: all

plugin: $(BUILD)/plugin/fst.extract
	@echo "[$(COMPONENT)] Building plugin"
	@dune build
.PHONY: plugin

$(BUILD)/plugin/fst.extract: $(ALL_CHECKED_FILES)
	@echo "[$(COMPONENT)] Extracting F*"
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) --extract $(FSTAR_EXTRACT_MODULES) --codegen Plugin --odir $(BUILD)/plugin/fst $(FSTAR_ALL_SRCS)
	@touch $@


