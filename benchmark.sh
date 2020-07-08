#!/bin/bash
echo "FOUR"
gerty benchmarks/bigApp4.lam --silent --benchmark --trials=10
gerty benchmarks/bigApp4.lam --silent --benchmark --tyc-optimise --trials=10
gerty benchmarks/bigApp4.lam --silent --benchmark --use-smt --trials=10
gerty benchmarks/bigApp4.lam --silent --benchmark --tyc-optimise --use-smt --trials=10

echo "FIVE"
gerty benchmarks/bigApp5.lam --silent --benchmark --trials=10
gerty benchmarks/bigApp5.lam --silent --benchmark --tyc-optimise --trials=10
gerty benchmarks/bigApp5.lam --silent --benchmark --use-smt --trials=10
gerty benchmarks/bigApp5.lam --silent --benchmark --tyc-optimise --use-smt --trials=10

echo "SIX"
gerty benchmarks/bigApp6.lam --silent --benchmark --trials=10
gerty benchmarks/bigApp6.lam --silent --benchmark --tyc-optimise --trials=10
gerty benchmarks/bigApp6.lam --silent --benchmark --use-smt --trials=10
gerty benchmarks/bigApp6.lam --silent --benchmark --tyc-optimise --use-smt --trials=10

echo "SEVEN"
gerty benchmarks/bigApp7.lam --silent --benchmark --trials=10
gerty benchmarks/bigApp7.lam --silent --benchmark --tyc-optimise --trials=10
gerty benchmarks/bigApp7.lam --silent --benchmark --use-smt --trials=10
gerty benchmarks/bigApp7.lam --silent --benchmark --tyc-optimise --use-smt --trials=10

echo "EIGHT"
gerty benchmarks/bigApp8.lam --silent --benchmark --trials=10
gerty benchmarks/bigApp8.lam --silent --benchmark --tyc-optimise --trials=10
gerty benchmarks/bigApp8.lam --silent --benchmark --use-smt --trials=10
gerty benchmarks/bigApp8.lam --silent --benchmark --tyc-optimise --use-smt --trials=10
