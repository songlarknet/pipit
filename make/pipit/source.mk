PIPIT_SOURCE_VANILLA_DEPS=$(PIPIT_CORE_DEPS) $(PIPIT_ABSTRACT_DEPS) $(PIPIT_EXTRACT_DEPS) pipit/source/
include $(BUILD)/source/deps.mk
verify-source: $(ALL_CHECKED_FILES)
verify: verify-source

$(BUILD)/source/deps.mk: FSTAR_INC_DIRS=$(PIPIT_SOURCE_VANILLA_DEPS)
$(BUILD)/source/deps.mk: FSTAR_SRC_DIRS=pipit/source/
