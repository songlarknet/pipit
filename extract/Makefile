# Run `make extract-c` to generate C code in gen/Example_Compile_Pump.c
# To generate for the other examples, use eg `make extract-c MODULE=Example.Compile.Simple`

FSTAR  ?= fstar.exe
KRML   ?= krml
MODULE ?= Example.Compile.Pump
SRC	   ?= ../src/

extract-c:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --extract $(MODULE) --codegen krml --odir gen
	cd gen && $(KRML) *.krml -skip-linking

extract-ocaml:
	@mkdir -p gen
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --extract $(MODULE) --codegen OCaml --odir gen
