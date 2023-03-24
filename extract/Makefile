FSTAR  ?= fstar.exe
KRML   ?= krml
MODULE ?= Example.Compile.Simple
SRC	   ?= ../src/

extract-c:
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --extract $(MODULE) --codegen krml
	$(KRML) out.krml -skip-compilation

extract-ocaml:
	$(FSTAR) $(SRC)/$(MODULE).fst --include $(SRC) --extract $(MODULE) --codegen OCaml
