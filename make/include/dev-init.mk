.PHONY: dev-init dev-refresh
FSTAR_PIN_REPO ?= https://github.com/songlarknet/FStar.git
FSTAR_PIN_HASH ?= 9f84ace78d4ac0355c1a6401a56bcd29e4a6318b
KARAMEL_PIN_REPO ?= https://github.com/songlarknet/karamel.git
KARAMEL_PIN_HASH ?= 3611ae497bb5ab8ae83207428c8a915653bd761c
UNAME_S := $(shell uname -s)
OPAM_MAKE ?= $(if $(filter Darwin,$(UNAME_S)),gmake,make)
OPAM_GNUBIN_DIR := $(firstword $(wildcard /opt/homebrew/opt/make/libexec/gnubin /usr/local/opt/make/libexec/gnubin))
OPAM_ENV_PREFIX := $(if $(filter Darwin,$(UNAME_S)),PATH=$(OPAM_GNUBIN_DIR):$$PATH,)

dev-init:
	@echo "* Setting up development environment"
#	@echo "* Checking for Python 2.7"
# XXX this is unnecessary for MacOS, so disable check
#	@python2.7 -c 'print "Python 2.7 OK"' || (echo 'Cannot find Python 2.7. FStar and Z3 need Python 2.7. See https://github.com/songlarknet/pipit#modern-linux-no-python-27'; exit 1)
	@echo "* Updating opam index"
	@$(OPAM_ENV_PREFIX) OPAMMAKE=$(OPAM_MAKE) opam update
	@echo "* Create a local opam switch with OCaml 5.3"
	@$(OPAM_ENV_PREFIX) OPAMMAKE=$(OPAM_MAKE) opam switch create . 5.3.0
	@echo "* Using OPAMMAKE=$(OPAM_MAKE)"
	@echo "* Using PATH prefix $(OPAM_GNUBIN_DIR)"
	@echo "* Bootstrapping ocamlfind and visitors in local switch"
	@$(OPAM_ENV_PREFIX) OPAMMAKE=$(OPAM_MAKE) opam install --switch . --yes --no-depexts ocamlfind visitors
	@echo "* Pinning F* to $(FSTAR_PIN_HASH)"
	@$(OPAM_ENV_PREFIX) OPAMMAKE=$(OPAM_MAKE) opam pin add fstar git+$(FSTAR_PIN_REPO)#$(FSTAR_PIN_HASH) --yes --no-depexts
	@echo "* Pinning karamel to $(KARAMEL_PIN_HASH)"
	@$(OPAM_ENV_PREFIX) LOWSTAR=false OPAMMAKE=$(OPAM_MAKE) opam pin add karamel git+$(KARAMEL_PIN_REPO)#$(KARAMEL_PIN_HASH) --yes --no-depexts
# no-depexts is required for Linux without Python 2.7 apt package

dev-refresh:
	@test -d _opam || (echo "_opam is missing. Run 'make dev-init' first."; exit 1)
	@echo "* Refreshing toolchain in existing local switch"
	@$(OPAM_ENV_PREFIX) OPAMMAKE=$(OPAM_MAKE) opam update
	@echo "* Using OPAMMAKE=$(OPAM_MAKE)"
	@echo "* Using PATH prefix $(OPAM_GNUBIN_DIR)"
	@echo "* Ensuring ocamlfind and visitors in local switch"
	@$(OPAM_ENV_PREFIX) OPAMMAKE=$(OPAM_MAKE) opam install --switch . --yes --no-depexts ocamlfind visitors
	@echo "* Re-pinning F* to $(FSTAR_PIN_HASH)"
	@$(OPAM_ENV_PREFIX) OPAMMAKE=$(OPAM_MAKE) opam pin add fstar git+$(FSTAR_PIN_REPO)#$(FSTAR_PIN_HASH) --yes --no-depexts
	@echo "* Re-pinning karamel to $(KARAMEL_PIN_HASH)"
	@$(OPAM_ENV_PREFIX) LOWSTAR=false OPAMMAKE=$(OPAM_MAKE) opam pin add karamel git+$(KARAMEL_PIN_REPO)#$(KARAMEL_PIN_HASH) --yes --no-depexts
