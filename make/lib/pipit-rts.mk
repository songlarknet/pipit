PIPIT_RTS_DEPS=pipit-rts/fstar/
include $(BUILD)/pipit-rts/deps.mk
all: $(ALL_CHECKED_FILES)

$(BUILD)/pipit-rts/deps.mk: FSTAR_INC_DIRS=$(PIPIT_RTS_DEPS)
$(BUILD)/pipit-rts/deps.mk: FSTAR_SRC_DIRS=pipit-rts/fstar/
