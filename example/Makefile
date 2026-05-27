ROOT_DIR 				?= ../..
PIPIT_DIR 			?= ../pipit
COMPONENT   		?= example
FSTAR_INC_DIRS 	?= base core rts/fstar abstract extract plugin/fst plugin/_build/default source
FSTAR_SRC_DIRS 	?= .
FSTAR_ALREADY_CACHED ?=

# Note: example/ttcan/ is currently disabled (see example/readme.md); it has
# its own dormant wiring and is not picked up here.

include $(ROOT_DIR)/make/include/base.mk

extract: $(BUILD)/Example.Simple.Extract.extract
extract: $(BUILD)/Example.Pump.Extract.extract

$(BUILD)/Example.Simple.Extract.extract: EXTRACT_MODULE=Example.Simple.Extract
$(BUILD)/Example.Simple.Extract.extract: EXTRACT_NAME=Example.Simple
$(BUILD)/Example.Simple.Extract.extract: EXTRACT_FILE=$(ROOT_DIR)/example/Example.Simple.Extract.fst

$(BUILD)/Example.Pump.Extract.extract: EXTRACT_MODULE=Example.Pump.Extract
$(BUILD)/Example.Pump.Extract.extract: EXTRACT_NAME=Example.Pump
$(BUILD)/Example.Pump.Extract.extract: EXTRACT_FILE=$(ROOT_DIR)/example/Example.Pump.Extract.fst

$(BUILD)/%.extract: $(BUILD)/cache/%.fst.checked
	@rm -f $(BUILD)/extract/$(EXTRACT_NAME)/*.krml
	@mkdir -p $(BUILD)/extract/$(EXTRACT_NAME)
# Do not extract Pipit modules -- all extractions should go in PipitRuntime.
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $(EXTRACT_FILE) --codegen krml --odir $(BUILD)/extract/$(EXTRACT_NAME) --extract '*' --extract '-Pipit'
	$(Q)cd $(BUILD)/extract/$(EXTRACT_NAME) && $(KARAMEL_EXE) *.krml -bundle $(EXTRACT_MODULE)=* -skip-linking -skip-makefiles $(KRML_OPT)
	@touch $@
