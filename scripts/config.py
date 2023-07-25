SOLVER_MAX_MEMORY = 25 * 1024

# Solver timeout (in seconds) or 0 for "no limit".
SOLVER_TIMEOUT = 5 * 60

# Size of anonymous memory size blocks we may need to introduce (for example,
# so that function pointer arguments have memory to point to).
ANON_MEM_SIZE = 64

# How many bytes load, store, __builtin_memset, etc. can expand.
MAX_MEMORY_UNROLL_LIMIT = 10000

# How the pointer bits are divided between id and offset.
PTR_OFFSET_BITS = 40
PTR_ID_BITS = 24
assert PTR_ID_BITS + PTR_OFFSET_BITS == 64
