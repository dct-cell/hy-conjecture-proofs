# Problem 41 — complete target

`Problem41/Spec.lean` defines the problem using actual ideals in `MvPolynomial (Fin 3) k` and monic equations for integral dependence. It does not import any proof module. `Problem41/Proof.lean` proves the fixed `Problem41.Claim`.

The expanded theorem `Problem41.complete_classification` quantifies over arbitrary fields and all positive integer triples, and gives equality with the integral closure for every positive power. The criterion is a terminating finite Boolean program using exact rational arithmetic.

The proof establishes both algebraic bridges: the integral closure of `(x^a,y^b,z^c)`, and the integral closure and monomial membership of every positive power. No bridge is assumed as an axiom.

## Reproduce

Lean 4.35.0 and all dependency commits are locked. With Lean installed, run in this directory:

```sh
lake exe cache get
./verify.sh
```

`verify.sh` runs `lake build`, then `--trust=0` on the specification, proof and audit entry points. The full target passed an independent clean local-module rebuild and all three kernel checks on 2026-11-09. The checked source commit is `8df3618d142283db73d0a2f4bbe4b124636e06f0`.

See [the complete log](verification.log), [commands, exit codes, versions and hashes](verification.json), and [the separate specification review](spec_review.json). The final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. No unproved axiom or placeholder occurs in its dependency closure.
