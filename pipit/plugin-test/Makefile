ROOT_DIR 				?= ../..
PIPIT_DIR 			?= ..
COMPONENT   		?= plugin-test
FSTAR_INC_DIRS 	?= base core rts/fstar abstract extract plugin/fst plugin/_build/default source
FSTAR_SRC_DIRS 	?= .
FSTAR_ALREADY_CACHED ?=


include $(ROOT_DIR)/make/include/base.mk

extract: $(BUILD)/Plugin.Test.Example.Simple.Extract.extract
extract: $(BUILD)/Plugin.Test.Example.Pump.Extract.extract

$(BUILD)/Plugin.Test.Example.Simple.Extract.extract: EXTRACT_MODULE=Plugin.Test.Example.Simple.Extract
$(BUILD)/Plugin.Test.Example.Simple.Extract.extract: EXTRACT_NAME=Plugin.Test.Example.Simple
$(BUILD)/Plugin.Test.Example.Simple.Extract.extract: EXTRACT_FILE=$(PIPIT_DIR)/plugin-test/Plugin.Test.Example.Simple.Extract.fst

$(BUILD)/Plugin.Test.Example.Pump.Extract.extract: EXTRACT_MODULE=Plugin.Test.Example.Pump.Extract
$(BUILD)/Plugin.Test.Example.Pump.Extract.extract: EXTRACT_NAME=Plugin.Test.Example.Pump
$(BUILD)/Plugin.Test.Example.Pump.Extract.extract: EXTRACT_FILE=$(PIPIT_DIR)/plugin-test/Plugin.Test.Example.Pump.Extract.fst

$(BUILD)/%.extract: $(BUILD)/cache/%.fst.checked
	@rm -f $(BUILD)/extract/$(EXTRACT_NAME)/*.krml
	@mkdir -p $(BUILD)/extract/$(EXTRACT_NAME)
# Do not extract Pipit modules -- all extractions should go in PipitRuntime.
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $(EXTRACT_FILE) --codegen krml --odir $(BUILD)/extract/$(EXTRACT_NAME) --extract '*' --extract '-Pipit'
	$(Q)cd $(BUILD)/extract/$(EXTRACT_NAME) && $(KARAMEL_EXE) *.krml -bundle $(EXTRACT_MODULE)=* -skip-linking -skip-makefiles $(KRML_OPT)
	@touch $@

