NUM_JOBS ?= $(shell nproc)
MAKEFLAGS := --jobs=$(NUM_JOBS)

ROOT_DIR = $(realpath .)
export ROOT_DIR

all: abstract base core extract plugin plugin-test source test rts example
.PHONY: all abstract base core extract plugin plugin-test source test rts example

clean:
	@rm -rf _build
.PHONY: clean


abstract: core
	@$(MAKE) -C pipit/abstract
abstract-%:
	@$(MAKE) -C pipit/abstract $(patsubst abstract-%,%,$@)

base: rts
	@$(MAKE) -C pipit/base
base-%:
	@$(MAKE) -C pipit/base $(patsubst base-%,%,$@)

core: base rts
	@$(MAKE) -C pipit/core
core-%:
	@$(MAKE) -C pipit/core $(patsubst core-%,%,$@)

extract: core rts abstract
	@$(MAKE) -C pipit/extract
extract-%:
	@$(MAKE) -C pipit/extract $(patsubst extract-%,%,$@)

plugin: core rts
	@$(MAKE) -C pipit/plugin
plugin-%:
	@$(MAKE) -C pipit/plugin $(patsubst plugin-%,%,$@)

plugin-test: source plugin
	@$(MAKE) -C pipit/plugin-test
plugin-test-%:
	@$(MAKE) -C pipit/plugin-test $(patsubst plugin-test-%,%,$@)


rts:
	@$(MAKE) -C pipit/rts
rts-%:
	@$(MAKE) -C pipit/rts $(patsubst rts-%,%,$@)

source: core abstract extract
	@$(MAKE) -C pipit/source
source-%:
	@$(MAKE) -C pipit/source $(patsubst source-%,%,$@)

test: extract source
	@$(MAKE) -C pipit/test
test-%:
	@$(MAKE) -C pipit/test $(patsubst test-%,%,$@)

example: extract source
	@$(MAKE) -C example
example-%:
	@$(MAKE) -C example $(patsubst example-%,%,$@)


include make/include/dev-init.mk

# DISABLED disable plugins for now, makefile issues mean that compiling core etc depends on plugin, but plugin depends on core
# include make/pipit/plugin.mk
# FSTAR_EXTRA_OPT:=$(FSTAR_EXTRA_OPT) --debug Plugin.Test.Language.Lift --ext pipit:lift:debug=1
# include make/pipit/plugin-test.mk
