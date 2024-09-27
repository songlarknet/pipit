PIPIT_BASE_DEPS=$(PIPIT_RTS_DEPS) pipit-base/
include $(BUILD)/pipit-base/deps.mk
all: $(ALL_CHECKED_FILES)

$(BUILD)/pipit-base/deps.mk: FSTAR_INC_DIRS=$(PIPIT_BASE_DEPS)
$(BUILD)/pipit-base/deps.mk: FSTAR_SRC_DIRS=pipit-base/
