PLUGIN_TEST_DIRS=pipit/plugin-test/
PLUGIN_TEST_DEPS=pipit/plugin-test/ $(PIPIT_EXTRACT_DEPS) $(PIPIT_SOURCE_VANILLA_DEPS) $(PLUGIN_DEPS) $(PLUGIN_TEST_DIRS)
include $(BUILD)/plugin-test/deps.mk
verify-plugin-test: $(ALL_CHECKED_FILES)
verify: verify-plugin-test

# Add dependency on built plugin - only applies to pipit/plugin-test/*.fst
# TODO better dep tracking
$(BUILD)/cache/Plugin.Test.*: $(PLUGIN_CMX_BIN)
# $(ALL_CHECKED_FILES): $(PLUGIN_CMX_BIN)

$(BUILD)/plugin-test/deps.mk: FSTAR_INC_DIRS=$(PLUGIN_TEST_DEPS)
$(BUILD)/plugin-test/deps.mk: FSTAR_SRC_DIRS=$(PLUGIN_TEST_DIRS)
