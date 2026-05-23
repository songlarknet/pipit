.PHONY: dev-init
FSTAR_PIN_REPO ?= https://github.com/songlarknet/FStar.git
FSTAR_PIN_HASH ?= 9f84ace78d4ac0355c1a6401a56bcd29e4a6318b
KARAMEL_PIN_REPO ?= https://github.com/songlarknet/karamel.git
KARAMEL_PIN_HASH ?= 3611ae497bb5ab8ae83207428c8a915653bd761c

dev-init:
	@echo "* Setting up development environment"
#	@echo "* Checking for Python 2.7"
# XXX this is unnecessary for MacOS, so disable check
#	@python2.7 -c 'print "Python 2.7 OK"' || (echo 'Cannot find Python 2.7. FStar and Z3 need Python 2.7. See https://github.com/songlarknet/pipit#modern-linux-no-python-27'; exit 1)
	@echo "* Updating opam index"
	@opam update
	@echo "* Create a local opam switch with OCaml 5.3"
	@opam switch create . 5.3.0
	@echo "* Pinning F* to $(FSTAR_PIN_HASH)"
	@opam pin add fstar git+$(FSTAR_PIN_REPO)#$(FSTAR_PIN_HASH) --yes --no-depexts
	@echo "* Pinning karamel to $(KARAMEL_PIN_HASH)"
	@opam pin add karamel git+$(KARAMEL_PIN_REPO)#$(KARAMEL_PIN_HASH) --yes --no-depexts
# no-depexts is required for Linux without Python 2.7 apt package
