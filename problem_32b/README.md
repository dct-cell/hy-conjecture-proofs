# Problem 32b: Two-v-generated Mori domains

[Problem](problem.md) · [HY result](hy_result.md) · [Original paper](https://www.mat.uniroma3.it/users/fontana/documents/CahenFontanaFrischGlaz_OpenProblemsArticle%20%282%29.pdf)

A complete counterexample over $\mathbb F_2$: the one-dimensional Mori domain $D=\mathbb F_2[[t^4,t^5,t^{11}]]$ has all nonzero divisorial ideals two-$v$-generated, but its maximal ideal is not stable.

Text review: complete.

Lean: **Full formalization verified on 2026-11-09.** The specification covers the fraction field, dimension one, the Mori condition, all nonzero divisorial ideals with generators not both zero, and the nonstable witness. `Spec.lean` is independent of the proof implementation.

The local proof modules were rebuilt from the verified source commit in a separate directory. The specification, proof entry point, and audit entry point passed `lean --trust=0`. The final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

[Lean project](Lean/) · [Full verification log](Lean/verification.log) · [Versions, hashes and audit metadata](Lean/verification.json) · [Historical verification, 2026-11-05](Lean/historical/2026-11-05/verification.json)

To reproduce, install the toolchain in `Lean/lean-toolchain`, then run:

```sh
cd problem_32b/Lean
lake exe cache get
./verify.sh
```

For a clean local-module rebuild, remove only `Lean/.lake/build` before running the checks. Dependency revisions are pinned by `lake-manifest.json`.
