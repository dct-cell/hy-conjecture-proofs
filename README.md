# Problem 32(b): a counterexample

**[HY result](model_outputs/hy_result.md)** — one clarifying sentence added;
math delimiters converted to `$...$` and `$$...$$`. No other changes to the
model answer. The Lean proof is subsequent work.

The question asks whether every divisorial ideal is stable in a one-dimensional
Mori domain whose divisorial ideals are all two-$v$-generated.
[Source: Cahen–Fontana–Frisch–Glaz, Problem 32(b), PDF page 14](https://www.mat.uniroma3.it/users/fontana/documents/CahenFontanaFrischGlaz_OpenProblemsArticle%20%282%29.pdf).

The counterexample is $D=k[[t^4,t^5,t^{11}]]$: every nonzero divisorial ideal is
two-$v$-generated, but its maximal ideal is not stable. The text works over
any field; Lean proves the complete counterexample for $k=\mathbb F_2$,
which suffices to refute the question. No priority claim is made.

## Lean

- [Spec.lean](Lean/Problem32b/Spec.lean): independent definitions and the original implication.
- [Proof.lean](Lean/Problem32b/Proof.lean): proves `Problem32b.refutation : ¬ Spec.Conjecture`.
- [Proofs/](Lean/Problem32b/Proofs/): the construction and supporting proofs.
- [Verification log](Lean/verification.log) and [versions, checks and hashes](Lean/verification.json).

The specification retains the fraction-field condition, Krull dimension exactly
one, the Mori ascending-chain condition, and **all** nonzero divisorial ideals.
Stability uses the ordinary ideal product in $(I:I)$. No Noetherian or monomial
restriction is added to the question. This correspondence was checked manually:
compiling a specification alone does not establish its mathematical fidelity.

The proof was rebuilt from clean local modules and checked with `--trust=0`.
Its axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`.
Lean is **4.35.0**; all dependency commits are fixed in `lake-manifest.json`.

With [elan](https://github.com/leanprover/elan) installed, reproduce with:

```sh
cd Lean
lake exe cache get
./verify.sh
```
