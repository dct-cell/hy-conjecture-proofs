# Problem 32(b)

Disprove the assertion below by constructing a domain and a divisorial ideal satisfying all its hypotheses but not its conclusion.

## Definitions

Let $D$ be a commutative integral domain with identity, with $1\ne 0$, and let $K=\operatorname{Frac}(D)$. A nonzero fractional ideal is a nonzero $D$-submodule $J\subseteq K$ with $dJ\subseteq D$ for some $0\ne d\in D$. For such $J$, define
$$
(D:J)=\{x\in K:xJ\subseteq D\},
\qquad
J^{v_D}=(D:(D:J)).
$$
A nonzero ideal $I\subseteq D$ is divisorial if $I=I^{v_D}$. It is two-generated with respect to $v_D$ if there exist $x,y\in I$, not both zero, such that
$$
I=(xD+yD)^{v_D}.
$$
The domain $D$ is Mori if every ascending chain of nonzero integral divisorial ideals of $D$ stabilizes. Its dimension is its Krull dimension, defined by lengths of strict chains of prime ideals.

For a nonzero ideal $I$ of $D$, define
$$
E(I)=(I:I)=\{z\in K:zI\subseteq I\},
\qquad
(E(I):I)=\{z\in K:zI\subseteq E(I)\}.
$$
The ring $E(I)$ contains $D$, and $I$ is an ideal of $E(I)$. The ideal $I$ is stable if it is invertible as an ideal of $E(I)$, meaning
$$
I(E(I):I)=E(I).
$$
The product is the set of finite sums of products of elements of the two factors.

## Assertion to disprove

For every domain $D$,
$$
\begin{gathered}
\dim D=1,\qquad D\text{ is Mori},\\
\forall\,0\ne J\subseteq D\text{ divisorial},\
\exists x,y\in J,\ (x,y)\ne(0,0),\
J=(xD+yD)^{v_D}
\\
\Longrightarrow
\\
\forall\,0\ne I\subseteq D\text{ divisorial},\
I(E(I):I)=E(I).
\end{gathered}
$$

## Completion requirements

Construct an explicit $D$ of dimension exactly one, prove that it is Mori, and verify the two-generator $v_D$ condition for every nonzero divisorial ideal of $D$. Then specify a nonzero divisorial ideal $I$ and prove that it is not stable. Verifying the two-generator condition only for the chosen $I$ is insufficient. All $v_D$ operations above are computed in $D$; stability uses ordinary ideal invertibility in $E(I)$. You may use established theorems, but state their precise forms and check their hypotheses.

Write the complete final solution to /workspace/proof.md and reproduce it in the final response.

Source: Problem 32(b), [original PDF](https://www.mat.uniroma3.it/users/fontana/documents/CahenFontanaFrischGlaz_OpenProblemsArticle%20%282%29.pdf).
