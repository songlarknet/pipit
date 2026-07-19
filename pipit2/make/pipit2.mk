# Shared configuration for pipit2 subpackages (core, plugin, plugin-test).
#
# pipit2 is a self-contained successor to pipit 1. All of its subpackages share
# ONE private cache dir -- separate from the shared $(BUILD)/cache used by
# pipit 1 -- so pipit2 module names can never collide with pipit 1's in the
# cache. Each subpackage still uses a distinct COMPONENT (pipit2-core, ...) so
# their generated deps.mk files land at distinct paths too.
#
# Include this BEFORE make/include/base.mk so these values win over base.mk's
# own `?=` defaults.
BUILD       ?= $(ROOT_DIR)/_build
CACHE_DIR   ?= $(BUILD)/pipit2/cache
FSTAR_CACHE ?= --cache_dir $(CACHE_DIR) --cache_checked_modules --already_cached Prims,FStar,LowStar,Pulse,PulseCore,$(FSTAR_ALREADY_CACHED)
