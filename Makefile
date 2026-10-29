# Avon.  `make` builds the release binary, `make check` runs the unit tests
# under ASan and UBSan and builds build/dbg/avon, a sanitized binary for
# tests/diff_aviary.py, which runs tests/drivers_check.sh too, `make smoke` runs tests/smoke.tsv's commands on the
# release binary (tests/smoke.sh), `make witness-check` runs tests/witness_check.sh,
# `make jet-witness-check` runs tests/jet_witness_check.sh,
# `make probe-witness-check` runs tests/probe_witness_check.sh,
# `make zk-jet-witness-check` runs tests/zk_jet_witness_check.sh,
# `make p2-witness-check` runs tests/p2_witness_check.sh,
# `make words-lean-check` runs tests/words_lean_check.sh,
# `make templates-lean-check` runs tests/templates_lean_check.sh,
# `make fix-lean-check` runs tests/fix_lean_check.sh,
# `make interp-lean-check` runs tests/interp_lean_check.sh,
# `make jets-lean-check` runs tests/jets_lean_check.sh (the last ten
# need a lean-ski checkout), `make selfhost-check` runs
# tests/selfhost_check.sh, `make front0-check` runs tests/front0_check.sh
# and `make front1-check` runs tests/front1_check.sh (the three need a
# skijack checkout), `make fixtures-check` runs tests/fixtures_check.sh
# (skijack, SKIlark and aviary), `make hider-check`
# runs tests/hider_check.sh (needs the pure-S paper's scripts); each runs
# at the revisions tests/pins.sh pins.  `make stats`
# builds build/stats/avon, which reports what becomes of template instances'
# cells (src/sstats.h), `make clean`
# removes build/.  Requires GNU Make 3.81+.

CC      := clang
# -std=c11 hides POSIX on glibc; _DEFAULT_SOURCE restores POSIX.1-2008 and
# the BSD calls (flock, mkdtemp) there, and macOS ignores it.
CSTD    := -std=c11 -D_DEFAULT_SOURCE
WARN    := -Wall -Wextra -Wpedantic -Werror -Wshadow -Wstrict-prototypes \
           -Wmissing-prototypes -Wconversion -Wno-sign-conversion
INC     := -Iinclude
RELEASE := -O2 -DNDEBUG
DEBUG   := -O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined \
           -fno-sanitize-recover=all

BUILD   := build
LIB_SRC := $(filter-out src/main.c,$(wildcard src/*.c))
CLI_SRC := src/main.c $(wildcard src/cli/*.c)     # the command, built into avon alone
TESTS   := $(wildcard tests/test_*.c)

REL_OBJ := $(patsubst src/%.c,$(BUILD)/rel/%.o,$(LIB_SRC))
DBG_OBJ := $(patsubst src/%.c,$(BUILD)/dbg/%.o,$(LIB_SRC))
TEST_BIN := $(patsubst tests/%.c,$(BUILD)/dbg/%,$(TESTS))

HDRS    := $(wildcard include/*.h src/*.h src/cli/*.h tests/*.h)

.PHONY: all check smoke clean stats witness-check jet-witness-check probe-witness-check zk-jet-witness-check p2-witness-check words-lean-check templates-lean-check fix-lean-check interp-lean-check jets-lean-check \
	selfhost-check front0-check front1-check fixtures-check hider-check
.SECONDARY:

all: $(BUILD)/avon

$(BUILD)/avon: $(CLI_SRC) $(REL_OBJ) $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) $(RELEASE) -o $@ $(CLI_SRC) $(REL_OBJ)

$(BUILD)/dbg/avon: $(CLI_SRC) $(DBG_OBJ) $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) $(DEBUG) -o $@ $(CLI_SRC) $(DBG_OBJ)

# build/stats/avon: the release build counting what becomes of template
# instances' cells (src/sstats.h), for one reduce or front0 run at a time.
STATS_OBJ := $(patsubst src/%.c,$(BUILD)/stats/%.o,$(LIB_SRC))

stats: $(BUILD)/stats/avon

$(BUILD)/stats/avon: $(CLI_SRC) $(STATS_OBJ) $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) $(RELEASE) -DAV_STRICT_STATS -o $@ $(CLI_SRC) $(STATS_OBJ)

$(BUILD)/stats/%.o: src/%.c $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) $(RELEASE) -DAV_STRICT_STATS -c -o $@ $<

$(BUILD)/rel/%.o: src/%.c $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) $(RELEASE) -c -o $@ $<

$(BUILD)/dbg/%.o: src/%.c $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) $(DEBUG) -c -o $@ $<

$(BUILD)/dbg/test_%: tests/test_%.c $(DBG_OBJ) $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) -Itests $(DEBUG) -o $@ $< $(DBG_OBJ)

check: $(TEST_BIN) $(BUILD)/dbg/avon
	@status=0; for t in $(TEST_BIN); do $$t || status=1; done; \
	tests/drivers_check.sh $(BUILD)/dbg/avon || status=1; exit $$status

# The release binary, asserts compiled out, against the outputs recorded from
# build/dbg/avon under ASan and UBSan.
smoke: $(BUILD)/avon
	tests/smoke.sh $(BUILD)/avon

# The witness strategy against lean-ski's aircheck and Plonky3 prover;
# needs a lean-ski checkout at $$LEAN_SKI (~/Code/ski/lean-ski).
witness-check: $(BUILD)/avon
	tests/witness_check.sh

jet-witness-check: $(BUILD)/avon
	tests/jet_witness_check.sh

probe-witness-check: $(BUILD)/avon
	tests/probe_witness_check.sh

zk-jet-witness-check: $(BUILD)/avon
	tests/zk_jet_witness_check.sh

p2-witness-check: $(BUILD)/avon
	tests/p2_witness_check.sh

words-lean-check:
	tests/words_lean_check.sh

templates-lean-check: $(BUILD)/avon
	tests/templates_lean_check.sh

fix-lean-check:
	tests/fix_lean_check.sh

interp-lean-check:
	tests/interp_lean_check.sh

jets-lean-check:
	tests/jets_lean_check.sh

selfhost-check: $(BUILD)/avon
	tests/selfhost_check.sh

front0-check: $(BUILD)/avon
	tests/front0_check.sh

front1-check: $(BUILD)/avon
	tests/front1_check.sh

# Every fixture another repository exports regenerates byte for byte at the
# revisions tests/pins.sh pins.
fixtures-check:
	tests/fixtures_check.sh

# Frame traces against the pure-S paper's hider census;
# needs the paper's scripts at $$HIDER_SCRIPTS.
hider-check: $(BUILD)/avon
	tests/hider_check.sh

clean:
	rm -rf $(BUILD)
