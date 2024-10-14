PIPIT_RTS_DEPS=pipit/rts/fstar/
include $(BUILD)/rts/deps.mk
verify: $(ALL_CHECKED_FILES)

$(BUILD)/rts/deps.mk: FSTAR_INC_DIRS=$(PIPIT_RTS_DEPS)
$(BUILD)/rts/deps.mk: FSTAR_SRC_DIRS=pipit/rts/fstar/
