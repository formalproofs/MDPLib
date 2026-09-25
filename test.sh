#!/usr/bin/env bash
#
# Check that MDPLib's main definitions are still computable at ℚ, then run the VaR
# regression suite both interpreted and natively compiled.
#
# Usage:
#   ./test.sh

set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"

lake build MDPLib

# 1. Elaboration: the plain `def`s and `#guard`s fire here, so a definition that turned
#    noncomputable, or a value that silently changed, fails the build.
lake env lean MDPLibTest.lean

# 2. Interpreted harness. `Main.main : IO Unit` never sets a non-zero exit code, so the
#    `--- N passed, M failed` summary is what has to be checked.
lake env lean --run Main.lean < test_var.json | tee /dev/stderr | grep -q -- '0 failed'

# 3. Native compilation and execution: the whole import closure goes through the compiler
#    backend, and the numbers come from compiled code rather than the interpreter.
lake build mdplib
./.lake/build/bin/mdplib < test_var.json | tee /dev/stderr | grep -q -- '0 failed'
