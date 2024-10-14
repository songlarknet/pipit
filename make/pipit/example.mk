EXAMPLE_DIRS=example/ example/ttcan/
EXAMPLE_DEPS=$(PIPIT_EXTRACT_DEPS) $(PIPIT_SOURCE_VANILLA_DEPS) $(EXAMPLE_DIRS)
include $(BUILD)/example/deps.mk
verify: $(ALL_CHECKED_FILES)

$(BUILD)/example/deps.mk: FSTAR_INC_DIRS=$(EXAMPLE_DEPS)
$(BUILD)/example/deps.mk: FSTAR_SRC_DIRS=$(EXAMPLE_DIRS)

.PHONY: extract
extract: extract-pump extract-simple extract-ttcan
all: extract

.PHONY: extract-pump
extract-pump: EXTRACT_MODULE=Pump.Extract
extract-pump: EXTRACT_FILE=example/Pump.Extract.fst
extract-pump: EXTRACT_NAME=pump
extract-pump: $(BUILD)/Pump.Extract.extract

.PHONY: extract-simple
extract-simple: EXTRACT_MODULE=Simple.Extract
extract-simple: EXTRACT_FILE=example/Simple.Extract.fst
extract-simple: EXTRACT_NAME=simple
extract-simple: $(BUILD)/Simple.Extract.extract

.PHONY: extract-ttcan
extract-ttcan: EXTRACT_MODULE=Network.TTCan.Extract
extract-ttcan: EXTRACT_FILE=example/ttcan/Network.TTCan.Extract.fst
extract-ttcan: EXTRACT_NAME=ttcan
extract-ttcan: $(BUILD)/Network.TTCan.Extract.extract

