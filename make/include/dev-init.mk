.PHONY: dev-init
dev-init:
	@echo "* Setting up development environment"
#	@echo "* Checking for Python 2.7"
# XXX this is unnecessary for MacOS, so disable check
#	@python2.7 -c 'print "Python 2.7 OK"' || (echo 'Cannot find Python 2.7. FStar and Z3 need Python 2.7. See https://github.com/songlarknet/pipit#modern-linux-no-python-27'; exit 1)
	@echo "* Updating opam index"
	@opam update
	@echo "* Create a local opam switch with OCaml 4.14"
	@opam switch create . 4.14.1
	@echo "* Updating / initialising git submodules"
	@git submodule update --init
	@echo "* Pinning development version of F*"
	@opam pin add fstar file://submodules/FStar --no-action
	@echo "* Pinning development version of karamel; building"
	@opam pin add karamel file://submodules/karamel --yes --no-depexts
# no-depexts is required for Linux without Python 2.7 apt package
