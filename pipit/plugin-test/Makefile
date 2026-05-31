ROOT_DIR 				?= ../..
PIPIT_DIR 			?= ..
COMPONENT   		?= plugin-test
FSTAR_INC_DIRS 	?= base core rts/fstar abstract extract plugin/fst plugin/_build/default source
FSTAR_SRC_DIRS 	?= .
FSTAR_ALREADY_CACHED ?=

# Silence F* warning 249 ("Losing precision when encoding a function literal")
# emitted by the SMT encoder for each Pulse [fn] splice (see comment above
# [mk_reset] / [mk_step] in [pipit/extract/Pipit.Exec.Pulse.fst]). Applied at
# the CLI level because an in-file pragma only catches half the warnings.
FSTAR_EXTRA_OPT += --warn_error -249

include $(ROOT_DIR)/make/include/base.mk

# Example extractions live in example/. Add new tests here if a plugin test
# needs a Pulse extract round-trip.

