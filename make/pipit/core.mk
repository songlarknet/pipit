PIPIT_CORE_DEPS=$(PIPIT_BASE_DEPS) $(PIPIR_RTS_DEPS) pipit/core/
include $(BUILD)/core/deps.mk
verify: $(ALL_CHECKED_FILES)

$(BUILD)/core/deps.mk: FSTAR_INC_DIRS=$(PIPIT_CORE_DEPS)
$(BUILD)/core/deps.mk: FSTAR_SRC_DIRS=pipit/core/
