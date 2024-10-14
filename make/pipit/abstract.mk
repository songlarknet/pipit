PIPIT_ABSTRACT_DEPS=$(PIPIT_CORE_DEPS) pipit/abstract/

include $(BUILD)/abstract/deps.mk
verify: $(ALL_CHECKED_FILES)

$(BUILD)/abstract/deps.mk: FSTAR_SRC_DIRS=$(PIPIT_ABSTRACT_DEPS)
$(BUILD)/abstract/deps.mk: FSTAR_INC_DIRS=pipit/abstract/
