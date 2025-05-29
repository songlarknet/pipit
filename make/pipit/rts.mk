PIPIT_RTS_DEPS=pipit/rts/fstar/
include $(BUILD)/rts/deps.mk
verify-rts: $(ALL_CHECKED_FILES)
verify: verify-rts

$(BUILD)/rts/deps.mk: FSTAR_INC_DIRS=$(PIPIT_RTS_DEPS)
$(BUILD)/rts/deps.mk: FSTAR_SRC_DIRS=pipit/rts/fstar/
