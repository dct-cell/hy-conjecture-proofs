# Problem 5(a)

Disprove the assertion that the global dimension of a commutative group ring is determined by the global dimension of its coefficient ring and the isomorphism type of its group, under the hypotheses below.

## Definitions

All rings are commutative with identity, with $1\ne 0$, and all modules are unital.

For a ring $R$, the projective dimension $\operatorname{pd}_R M$ of an $R$-module $M$ is the least length of a projective resolution of $M$, or $\infty$ if no finite projective resolution exists. A module is projective if it is a direct summand of a free module. The global dimension is
$$
\operatorname{gl.dim}R=\sup\{\operatorname{pd}_R M:M\text{ is an }R\text{-module}\},
$$
where the supremum ranges over all modules, not only finitely generated ones.

For an abelian group $G$, the group ring $R[G]$ consists of finite formal sums $\sum_{g\in G}r_g[g]$, with coefficients in $R$, componentwise addition, and multiplication determined by $[g][h]=[gh]$ and distributivity.

A pair $(R,G)$ is admissible if, for every element $g\in G$ of finite order $n$, the element $n\cdot 1_R$ is a unit of $R$. No finiteness or finite generation assumption is imposed on $G$.

## Assertion to disprove

For any abelian group $G$ and any rings $R_1,R_2$ for which both $(R_1,G)$ and $(R_2,G)$ are admissible,
$$
\operatorname{gl.dim}R_1=\operatorname{gl.dim}R_2
\quad\Longrightarrow\quad
\operatorname{gl.dim}R_1[G]=\operatorname{gl.dim}R_2[G].
$$

Construct explicit $R_1,R_2,G$ that refute this implication. Verify the unit condition for every finite-order element of $G$, prove equality of the two coefficient-ring global dimensions, and prove that the two group-ring global dimensions are different. The comparison must concern the same group, or groups whose isomorphism is established.

## Completion requirements

Give a complete counterexample with rigorous verification of all hypotheses and of the failure of the conclusion. An example violating the unit condition does not complete the task. You may use established theorems, but state their precise forms and check their hypotheses.

Write the complete final solution to /workspace/proof.md and reproduce it in the final response.

Source: Problem 5(a), [original PDF](https://www.mat.uniroma3.it/users/fontana/documents/CahenFontanaFrischGlaz_OpenProblemsArticle%20%282%29.pdf).
