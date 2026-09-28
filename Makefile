# Avon.  `make` builds the release binary, `make check` runs the unit tests
# under ASan and UBSan and builds build/dbg/avon, a sanitized binary for
# tests/diff_aviary.py, `make witness-check` runs tests/witness_check.sh,
# `make jet-witness-check` runs tests/jet_witness_check.sh,
# `make clean` removes build/.  Requires GNU Make 3.81+.

CC      := clang
CSTD    := -std=c11
WARN    := -Wall -Wextra -Wpedantic -Werror -Wshadow -Wstrict-prototypes \
           -Wmissing-prototypes -Wconversion -Wno-sign-conversion
INC     := -Iinclude
RELEASE := -O2 -DNDEBUG
DEBUG   := -O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined \
           -fno-sanitize-recover=all

BUILD   := build
LIB_SRC := $(filter-out src/main.c,$(wildcard src/*.c))
TESTS   := $(wildcard tests/test_*.c)

REL_OBJ := $(patsubst src/%.c,$(BUILD)/rel/%.o,$(LIB_SRC))
DBG_OBJ := $(patsubst src/%.c,$(BUILD)/dbg/%.o,$(LIB_SRC))
TEST_BIN := $(patsubst tests/%.c,$(BUILD)/dbg/%,$(TESTS))

HDRS    := $(wildcard include/*.h src/*.h tests/*.h)

.PHONY: all check clean witness-check jet-witness-check
.SECONDARY:

all: $(BUILD)/avon

$(BUILD)/avon: src/main.c $(REL_OBJ) $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) $(RELEASE) -o $@ src/main.c $(REL_OBJ)

$(BUILD)/dbg/avon: src/main.c $(DBG_OBJ) $(HDRS)
	@mkdir -p $(@D)
	$(CC) $(CSTD) $(WARN) $(INC) $(DEBUG) -o $@ src/main.c $(DBG_OBJ)

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
	@status=0; for t in $(TEST_BIN); do $$t || status=1; done; exit $$status

# The witness strategy against lean-ski's aircheck and Plonky3 prover
# (docs/DESIGN.md §17); needs a lean-ski checkout at $$LEAN_SKI (~/lean-ski).
witness-check: $(BUILD)/avon
	tests/witness_check.sh

jet-witness-check: $(BUILD)/avon
	tests/jet_witness_check.sh

clean:
	rm -rf $(BUILD)
