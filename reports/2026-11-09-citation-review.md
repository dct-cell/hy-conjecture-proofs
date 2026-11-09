# Citation review and Lean recheck — 2026-11-09

The six HY results now include references at the points of use and a bibliography with links and theorem, section or page locators. The evaluation statements, counterexamples, main conclusions and quantified scopes are unchanged.

| Problem | Manuscript update |
|---|---|
| [5a](../problem_05a/hy_result.md) | Sources for Maschke's theorem, the projective-dimension inequality and Schanuel's lemma. |
| [32b](../problem_32b/hy_result.md) | Sources for Noetherian formal power-series rings and dimension under integral extensions. |
| [37c](../problem_37c/hy_result.md) | Precise construction attribution and valuation references; “there is one” is clarified as existence, not uniqueness. |
| [41](../problem_41/hy_result.md) | References for integral closure and Rees algebras. The manuscript retains its proof of the finite classification criterion. |
| [43](../problem_43/hy_result.md) | The published theorem and definition numbers, and sources for normality, Cohen–Macaulayness, excellence and openness of Serre loci. |
| [44](../problem_44/hy_result.md) | Sources for contraction, plumbing, completion, Rees valuations and elliptic curves; expanded explanations of the plumbing neighborhoods and the comparison of analytic and algebraic blowup charts. |

References were checked for their stated hypotheses and the facts used. The Grauert formulation and Sally completion theorem are explicitly attributed to the checked expositions where they are quoted. The references do not imply that the manuscripts are independent of earlier literature or that all six results are new.

All original displayed and inline formulas remain present. The additional formulas in Problem 44 describe the same chart-completion argument. All six `problem.md` files are byte-for-byte unchanged.

## Completed Lean developments

No Lean source change is required by these manuscript edits. All 58 tracked source, specification, toolchain, dependency-lock and build-script files across Problems 5a, 32b and 41 are byte-for-byte unchanged from commit `72944e9bddb22c2aa8f26ebd77187240e4e48834`.

Each project was copied to an independent build directory without its local proof build products. Pinned dependency caches were reused, with every dependency revision checked against `lake-manifest.json`. The following commands were actually run for each project (`XX` is `05a`, `32b` or `41`):

```sh
lean --version
lake --version
lake build
lake env lean --trust=0 ProblemXX/Spec.lean
lake env lean --trust=0 ProblemXX/Proof.lean
lake env lean --trust=0 Audit.lean
```

All 18 commands exited with code 0. The toolchain is Lean 4.35.0; mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`. The final theorem types and specification definitions were printed and checked. The 19 printed, distinct axiom closures contain only `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx` or additional computation-trust axiom.

| Problem | Checked scope | Fresh evidence |
|---|---|---|
| 5a | The common group, order-invertibility conditions and all four exact global dimensions, quantified over arbitrary modules. | [Log](../problem_05a/Lean/verification.log), [commands, revisions and hashes](../problem_05a/Lean/verification.json) |
| 32b | The actual fraction field, dimension one, the Mori condition, generation of every nonzero divisorial ideal by two elements under the $v$-operation, and a nonstable divisorial ideal. Colons and ordinary products retain their stated ambient rings. | [Log](../problem_32b/Lean/verification.log), [commands, revisions and hashes](../problem_32b/Lean/verification.json) |
| 41 | The actual polynomial ideal, its integral closure, all positive powers, and equivalence with the terminating finite test for every positive triple over every field. | [Log](../problem_41/Lean/verification.log), [commands, revisions and hashes](../problem_41/Lean/verification.json) |

The logs and metadata above are from this recheck, conducted from 06:14 to 06:19 UTC on 2026-11-09. Earlier records remain in Git history. Existing style and module-import warnings do not affect the successful checks.

Problems 37c, 43 and 44 still have partial local formalizations. This citation update does not claim complete Lean verification of those three problems.
