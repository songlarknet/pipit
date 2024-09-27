PIPIT_SOURCE_VANILLA_DEPS=$(PIPIT_CORE_DEPS) $(PIPIT_ABSTRACT_DEPS) $(PIPIT_EXTRACT_DEPS) pipit-source-vanilla/
include $(BUILD)/pipit-source-vanilla/deps.mk
all: $(ALL_CHECKED_FILES)

$(BUILD)/pipit-source-vanilla/deps.mk: FSTAR_INC_DIRS=$(PIPIT_SOURCE_VANILLA_DEPS)
$(BUILD)/pipit-source-vanilla/deps.mk: FSTAR_SRC_DIRS=pipit-source-vanilla/
