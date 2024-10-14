TEST_DIRS=pipit/test/
TEST_DEPS=$(PIPIT_EXTRACT_DEPS) $(PIPIT_SOURCE_VANILLA_DEPS) $(EXAMPLE_DIRS)
include $(BUILD)/test/deps.mk
verify: $(ALL_CHECKED_FILES)

$(BUILD)/test/deps.mk: FSTAR_INC_DIRS=$(TEST_DEPS)
$(BUILD)/test/deps.mk: FSTAR_SRC_DIRS=$(TEST_DIRS)
