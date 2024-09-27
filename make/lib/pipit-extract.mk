PIPIT_EXTRACT_DEPS=$(PIPIT_CORE_DEPS) $(PIPIT_RTS_DEPS) $(PIPIT_ABSTRACT_DEPS) pipit-extract/
include $(BUILD)/pipit-extract/deps.mk
all: $(ALL_CHECKED_FILES)

$(BUILD)/pipit-extract/deps.mk: FSTAR_INC_DIRS=$(PIPIT_EXTRACT_DEPS)
$(BUILD)/pipit-extract/deps.mk: FSTAR_SRC_DIRS=pipit-extract/
