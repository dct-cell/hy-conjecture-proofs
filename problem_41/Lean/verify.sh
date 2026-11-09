#!/bin/sh
# Rebuild the project and check the specification, proof and audit with the kernel.
set -eu
cd "$(dirname "$0")"
lean --version
lake --version
lake build
lake env lean --trust=0 Problem41/Spec.lean
lake env lean --trust=0 Problem41/Proof.lean
lake env lean --trust=0 Audit.lean
