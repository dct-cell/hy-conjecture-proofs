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

`verify.sh` runs `lake build`, then `--trust=0` on the specification, proof and audit entry points. A fresh audit of this source commit is pending; no historical log is used for it.
