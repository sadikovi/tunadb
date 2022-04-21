#!/bin/bash

bin="`dirname "$0"`"
ROOT_DIR="`cd "$bin/../"; pwd`"

# Export backtrace for easier debugging
export RUST_BACKTRACE=1

FUZZ_TESTS=(
  test_storage_manager_fuzz_free_fully
  test_storage_manager_fuzz_free_with_writes
  test_util_lru_fuzz_update_evict
  test_btree_fuzz_byte_put_get_del
  test_btree_fuzz_unique_put_get_del
  test_btree_fuzz_byte_put_range
)

NUM_ITERATIONS=100

for t in ${FUZZ_TESTS[@]}; do
  echo "== Running $t =="
  for i in $(seq 0 $NUM_ITERATIONS); do
    echo "  [$i] iteration"
    cargo test $t
    if [[ $? -ne 0 ]]; then
      echo "Test $t FAILED"
      exit 1;
    fi
  done
done

echo "All tests passed"
