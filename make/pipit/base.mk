PIPIT_BASE_DEPS=$(PIPIT_RTS_DEPS) pipit/base/
include $(BUILD)/base/deps.mk
verify-base: $(ALL_CHECKED_FILES)
verify: verify-base

$(BUILD)/base/deps.mk: FSTAR_INC_DIRS=$(PIPIT_BASE_DEPS)
$(BUILD)/base/deps.mk: FSTAR_SRC_DIRS=pipit/base/
