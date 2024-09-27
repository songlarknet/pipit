all:

include make/include/dev-init.mk

include make/include/base.mk
include make/include/verify.mk
include make/include/extract.mk

ifneq (, $(shell which $(FSTAR_EXE)))

include make/lib/pipit-rts.mk
include make/lib/pipit-base.mk
include make/lib/pipit-core.mk
include make/lib/pipit-abstract.mk
include make/lib/pipit-extract.mk
include make/lib/pipit-source-vanilla.mk

include make/lib/example.mk
include make/lib/test.mk

endif
