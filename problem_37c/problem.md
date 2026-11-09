# Problem 37(c)

Disprove the assertion below while retaining all the stated algebra embeddings and finiteness assumptions.

## Definitions

All domains are commutative with identity, with $1\ne 0$, and all embeddings preserve the identity.

The Krull dimension $\dim R$ of a ring is the supremum of the lengths of strict chains of prime ideals. A domain $R$ is Jaffard if its Krull dimension is finite and
$$
\dim R[X_1,\ldots,X_n]=\dim R+n
\qquad\text{for every integer }n\ge 1,
$$
where the $X_i$ are indeterminates.

A domain $D$ is locally Jaffard if $D_P$ is Jaffard for every prime ideal $P$ of $D$, where
$$
D_P=\{a/s:a\in D,\ s\in D\setminus P\}
\subseteq\operatorname{Frac}(D).
$$
An affine domain over a domain $A$ is an integral domain $T$ containing $A$ that is finitely generated as an $A$-algebra. A ring is Noetherian if every ideal is finitely generated.

## Assertion to disprove

For every Noetherian integral domain $A$, every affine domain $T$ over $A$, and every intermediate $A$-subalgebra
$$
A\subseteq D\subseteq T,
$$
the domain $D$ is locally Jaffard.

No finite generation assumption is imposed on $D$ as an $A$-algebra.

## Completion requirements

Construct explicit $A,D,T$ and their compatible embeddings. Prove that $A$ is Noetherian, that $T$ is an integral domain finitely generated over $A$, and that $D$ is an intermediate $A$-subalgebra. Exhibit a prime ideal $P$ of $D$ and prove that $D_P$ fails the definition of a Jaffard domain. A failure of some different finiteness property of $D$ is not sufficient. You may use established theorems, but state their precise forms and check their hypotheses.

Write the complete final solution to /workspace/proof.md and reproduce it in the final response.

Source: Problem 37(c), [original PDF](https://www.mat.uniroma3.it/users/fontana/documents/CahenFontanaFrischGlaz_OpenProblemsArticle%20%282%29.pdf).
