#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
lean --version
lake --version
lake build
lake env lean --trust=0 Problem32b/Spec.lean
lake env lean --trust=0 Audit.lean
