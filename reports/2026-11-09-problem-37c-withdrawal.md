# Problem 37(c): removed from the current collection

On 2026-11-09, Problem 37(c) was removed from this repository's current collection at the owner's request, and its local Lean development was stopped. The other five problem directories are unchanged.

## Source correspondence

Viet-Hoang Tran, Thieu N. Vo and Tan M. Nguyen, *Bouvier’s conjecture is true*, arXiv:2609.01887v1, §2.4 and Corollary 5.7, explicitly give a negative answer to Problem 37(c).

Corollary 5.7 supplies a field $k$, domains $R$ and $T$, and a prime $P$ of $R$ such that

$$
k\subseteq R\subseteq T=k[\pi,\pi^{-1},x_0,y_0,z_0],
\qquad
\dim R_P=2,
\qquad
\dim R_P[X]=4.
$$

Thus the base $k$ is Noetherian, $T$ is an affine $k$-domain, and the intermediate $k$-subalgebra $R$ has a localization that is not Jaffard. These are the precise hypotheses and failure required by the evaluation statement. The HY manuscript already attributed its construction to this preprint.

- [Original problem collection, Problem 37(c)](https://www.mat.uniroma3.it/users/fontana/documents/CahenFontanaFrischGlaz_OpenProblemsArticle%20%282%29.pdf).
- [Version 1, §2.4: explicit correspondence with Problem 37(c)](https://arxiv.org/html/2609.01887v1#S2.SS4).
- [Version 1, Corollary 5.7: the affine-subalgebra counterexample](https://arxiv.org/html/2609.01887v1#S5.SS7).
- [arXiv version history](https://arxiv.org/abs/2609.01887). Version 1 was submitted on 2026-09-01; version 2 is dated 2026-09-13 and is titled *Bouvier’s Conjecture and Dimension Sequences of Unique Factorization Domains*. The direct Problem 37(c) statement cited above is in version 1.

This records an existing public preprint solution, not a claim of journal peer review. Removal is based on the prior construction and the owner's requested scope; it does not assert that the HY argument is false. No complete Lean verification of Problem 37(c) is claimed.

The removed evaluation statement and HY manuscript remain in [commit 00eec591](https://github.com/dct-cell/hy-conjecture-proofs/tree/00eec591a06b4c05c25efb3868b40edf6b8afa37/problem_37c). Local manuscripts and formalization work were retained.
