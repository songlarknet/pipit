ROOT_DIR 				?= ..
PIPIT_DIR 			?= ../pipit
COMPONENT   		?= example
FSTAR_INC_DIRS 	?= base core rts/fstar abstract extract source
FSTAR_SRC_DIRS 	?= .
FSTAR_ALREADY_CACHED ?=


include $(ROOT_DIR)/make/include/base.mk
# include $(ROOT_DIR)/make/include/extract.mk

# TODO: extraction is disabled

# all: extract
extract: $(BUILD)/Pump.Extract.extract
extract: $(BUILD)/Simple.Extract.extract

$(BUILD)/Pump.Extract.extract: EXTRACT_MODULE=Pump.Extract
$(BUILD)/Pump.Extract.extract: EXTRACT_NAME=Pump
$(BUILD)/Pump.Extract.extract: EXTRACT_FILE=$(ROOT_DIR)/example/Pump.Extract.fst

$(BUILD)/Simple.Extract.extract: EXTRACT_MODULE=Simple.Extract
$(BUILD)/Simple.Extract.extract: EXTRACT_NAME=Simple
$(BUILD)/Simple.Extract.extract: EXTRACT_FILE=$(ROOT_DIR)/example/Simple.Extract.fst

$(BUILD)/%.extract: $(BUILD)/cache/%.fst.checked
	@rm -f $(BUILD)/extract/$(EXTRACT_NAME)/*.krml
	@mkdir -p $(BUILD)/extract/$(EXTRACT_NAME)
# Do not extract Pipit modules -- all extractions should go in PipitRuntime.
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $(EXTRACT_FILE) --codegen krml --odir $(BUILD)/extract/$(EXTRACT_NAME) --extract '*' --extract '-Pipit'
	$(Q)cd $(BUILD)/extract/$(EXTRACT_NAME) && $(KARAMEL_EXE) *.krml -bundle $(EXTRACT_MODULE)=* -skip-linking -skip-compilation -skip-makefiles $(KRML_OPT)
	@touch $@
