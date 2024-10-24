all:

include make/include/dev-init.mk

include make/include/base.mk
include make/include/verify.mk
include make/include/extract.mk

ifneq (, $(shell which $(FSTAR_EXE)))

include make/pipit/rts.mk
include make/pipit/base.mk
include make/pipit/core.mk
include make/pipit/abstract.mk
include make/pipit/extract.mk
include make/pipit/source.mk

include make/pipit/example.mk
include make/pipit/test.mk

include make/pipit/plugin.mk
include make/pipit/plugin-test.mk

endif
