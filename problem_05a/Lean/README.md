# Problem 5a: formal counterexample

The specification and proof are separate. `Problem05a/Spec.lean` defines the actual additive group algebra, global dimension (over all modules), admissibility, and the four required dimensions. It does not import the proof.

The final theorem `Problem05a.solution` proves, with

- `G = ℕ →₀ ZMod 2`,
- `A = AddMonoidAlgebra (ZMod 3) G`,
- `B = Polynomial (ZMod 3)`,

that both coefficient rings satisfy the torsion-order invertibility condition, and

```text
gldim A = 1,  gldim B = 1,
gldim A[G] = 1,  gldim B[G] = 2.
```

The universe-polymorphic theorem includes arbitrary modules, without a finite-generation restriction. `Problem05a.expanded_counterexample` exposes the module quantifiers and strict lower bounds.

The proof establishes projectivity of every ideal of the countable rings satisfying `x^3 = x`, derives the global bound via Baer's criterion, and proves strict lower bounds using augmentation. For the polynomial extension it constructs the exact sequence of polynomial modules, proves preservation of the dimension bound under flat scalar extension, and exhibits a nonprojective ideal. The final group-algebra identification is an actual ring equivalence.

## Rebuild

Install the toolchain named in `lean-toolchain`, then run:

```sh
./verify.sh
```

`lake-manifest.json` fixes mathlib and all transitive dependencies. The verification records include a fresh build in a separate source directory, kernel checks with `--trust=0`, final theorem types, axiom dependencies, commands, exit codes, and source hashes. Dependency build caches may be reused; the recorded fresh build starts without any local proof-module build products.

`spec_review.json` records the separate mathematical correspondence check. Kernel verification checks the formal theorem; it does not replace this review of the specification.
