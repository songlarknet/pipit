PIPIT_SOURCE_VANILLA_DEPS=$(PIPIT_CORE_DEPS) $(PIPIT_ABSTRACT_DEPS) $(PIPIT_EXTRACT_DEPS) pipit/source/
include $(BUILD)/source/deps.mk
verify: $(ALL_CHECKED_FILES)

$(BUILD)/source/deps.mk: FSTAR_INC_DIRS=$(PIPIT_SOURCE_VANILLA_DEPS)
$(BUILD)/source/deps.mk: FSTAR_SRC_DIRS=pipit/source/
