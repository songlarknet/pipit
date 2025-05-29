PIPIT_EXTRACT_DEPS=$(PIPIT_CORE_DEPS) $(PIPIT_RTS_DEPS) $(PIPIT_ABSTRACT_DEPS) pipit/extract/
include $(BUILD)/extract/deps.mk
verify-extract: $(ALL_CHECKED_FILES)
verify: verify-extract

$(BUILD)/extract/deps.mk: FSTAR_INC_DIRS=$(PIPIT_EXTRACT_DEPS)
$(BUILD)/extract/deps.mk: FSTAR_SRC_DIRS=pipit/extract/
