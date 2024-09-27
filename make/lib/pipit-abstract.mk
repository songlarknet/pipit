PIPIT_ABSTRACT_DEPS=$(PIPIT_CORE_DEPS) pipit-abstract/

include $(BUILD)/pipit-abstract/deps.mk
all: $(ALL_CHECKED_FILES)

$(BUILD)/pipit-abstract/deps.mk: FSTAR_SRC_DIRS=$(PIPIT_ABSTRACT_DEPS)
$(BUILD)/pipit-abstract/deps.mk: FSTAR_INC_DIRS=pipit-abstract/
