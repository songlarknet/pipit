PLUGIN_TEST_DIRS=pipit/plugin-test/
PLUGIN_TEST_DEPS=pipit/plugin-test/ $(PIPIT_EXTRACT_DEPS) $(PIPIT_SOURCE_VANILLA_DEPS) $(PLUGIN_DEPS) $(PLUGIN_TEST_DIRS)
include $(BUILD)/plugin-test/deps.mk
verify: $(ALL_CHECKED_FILES)

# Add dependency on built plugin - only applies to pipit/plugin-test/*.fst
$(ALL_CHECKED_FILES): $(PLUGIN_CMX_BIN)

$(BUILD)/plugin-test/deps.mk: FSTAR_INC_DIRS=$(PLUGIN_TEST_DEPS)
$(BUILD)/plugin-test/deps.mk: FSTAR_SRC_DIRS=$(PLUGIN_TEST_DIRS)
