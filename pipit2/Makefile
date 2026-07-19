# pipit2: successor experiment (self-contained; see ../doc/roadmap/).
#
# This is a dispatcher over the pipit2 subpackages, mirroring the repo root
# Makefile. The subpackages share one private cache dir (see make/pipit2.mk) so
# their module names cannot collide with pipit 1's in the shared cache.
#
#   core         F* core language: exp AST, source Stream layer, transforms,
#                the bool example + sofar_and rule.
#   plugin       extracts the core to an OCaml `#lang-pipit` plugin.
#   plugin-test  F* tests exercising the source -> rewrite path.

# Resolve ROOT_DIR to an absolute path so it is correct in the subpackages
# regardless of whether pipit2 is built from the repo root or standalone.
ROOT_DIR ?= $(realpath ..)
export ROOT_DIR

all: core plugin plugin-test
.PHONY: all core plugin plugin-test clean

core:
	@$(MAKE) -C core
core-%:
	@$(MAKE) -C core $(patsubst core-%,%,$@)

plugin: core
	@$(MAKE) -C core extract
	@$(MAKE) -C plugin
plugin-%:
	@$(MAKE) -C plugin $(patsubst plugin-%,%,$@)

plugin-test: core plugin
	@$(MAKE) -C plugin-test
plugin-test-%:
	@$(MAKE) -C plugin-test $(patsubst plugin-test-%,%,$@)

clean:
	@$(MAKE) -C core clean
	@$(MAKE) -C plugin clean
	@$(MAKE) -C plugin-test clean
