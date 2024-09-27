PIPIT_CORE_DEPS=$(PIPIT_BASE_DEPS) $(PIPIR_RTS_DEPS) pipit-core/
include $(BUILD)/pipit-core/deps.mk
all: $(ALL_CHECKED_FILES)

$(BUILD)/pipit-core/deps.mk: FSTAR_INC_DIRS=$(PIPIT_CORE_DEPS)
$(BUILD)/pipit-core/deps.mk: FSTAR_SRC_DIRS=pipit-core/
