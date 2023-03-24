# Run `make extract-c` to generate C code in gen/Example_Compile_Simple.c

FSTAR  ?= fstar.exe
KRML   ?= krml
MODULE ?= Example.Compile.Simple
SRC	   ?= ../src/

extract-c:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --extract $(MODULE) --codegen krml --odir gen
	cd gen && $(KRML) *.krml -skip-compilation

extract-ocaml:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --extract $(MODULE) --codegen OCaml --odir gen
