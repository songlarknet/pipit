TEST_DIRS=pipit/test/
TEST_DEPS=$(PIPIT_EXTRACT_DEPS) $(PIPIT_SOURCE_VANILLA_DEPS) $(EXAMPLE_DIRS)
include $(BUILD)/test/deps.mk
verify-test: $(ALL_CHECKED_FILES)
verify: verify-test

$(BUILD)/test/deps.mk: FSTAR_INC_DIRS=$(TEST_DEPS)
$(BUILD)/test/deps.mk: FSTAR_SRC_DIRS=$(TEST_DIRS)
