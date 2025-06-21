
$(BUILD)/%.extract: _build/cache/%.fst.checked
	@echo "* Extracting $(EXTRACT_MODULE)"
	@rm -f $(BUILD)/extract/$(EXTRACT_NAME)/*.krml
	@mkdir -p $(BUILD)/extract/$(EXTRACT_NAME)
# Do not extract Pipit modules -- all extractions should go in PipitRuntime.
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $(EXTRACT_FILE) --codegen krml --odir $(BUILD)/extract/$(EXTRACT_NAME) --extract '*' --extract '-Pipit'
	$(Q)cd $(BUILD)/extract/$(EXTRACT_NAME) && $(KARAMEL_EXE) *.krml -bundle $(EXTRACT_MODULE)=* -skip-linking -skip-compilation -skip-makefiles $(KRML_OPT)
	$(Q)touch $@
