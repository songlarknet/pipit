.PHONY: all
all: verify


%.fst.checked:
	@echo "* Checking: $<"
	$(Q)$(FSTAR_EXE) $(FSTAR_OPT) $<
	@touch -c $@

.PHONY: verify
verify: $(ALL_CHECKED_FILES)

# `make verify-retry`:
# Sometimes the proofs are flaky during development, so it can be useful to
# build with retries enabled.
verify-retry: FSTAR_PROOF_OPT=--retry 2
verify-retry: verify