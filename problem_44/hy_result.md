# Solution to Problem 44

We specify a complex-analytic surface germ by plumbing two explicitly given line bundles on an explicitly given elliptic curve, contract the two compact curves by Grauert’s theorem, and then complete the resulting analytic local ring.

Two preliminary points deserve emphasis. First, all choices which are merely asserted to exist in Cutkosky’s construction are made explicit here: the elliptic curve, its point, and the two normal bundles. Secondly, the argument below is organized so that it proves the required assertion for *every* ideal in the sense of the problem. We prove the assertion first for the analytic local ring $A$, where all blowups are analytic, and then use Sally’s completion theorem to pass to $\widehat A$. We also use a high Veronese subalgebra of the normalized Rees algebra: this bridges the difference between “one Rees valuation ring” (normalized blowup has one component) and “the ordinary blowup is already normal and has one component.” This distinction is important and is not merely terminological.

## 1. Standard results used

We use the following results in these precise forms.

**(G) Grauert contraction.** Let $C=C_1\cup\cdots\cup C_r$ be a connected compact reduced curve, with smooth components and transverse intersections, on a smooth complex surface $V$. If the intersection matrix $(C_i\cdot C_j)$ is negative definite, then, after replacing $V$ by a sufficiently small analytic neighborhood of $C$, there is a proper bimeromorphic holomorphic map
$$
g:V\to W
$$
to a normal complex-analytic surface $W$, an isomorphism away from $C$, which contracts $C$ to one point $q$. The analytic germ $(W,q)$ is determined by the germ of $V$ along $C$.

**(E) Analytic excellence and completion.** Complex-analytic local rings are excellent. If $A$ is an excellent normal local ring, then $\widehat A$ is normal; as $\widehat A$ is local, it is a domain. Moreover $\dim\widehat A=\dim A$.

**(R) Rees’s geometric description.** For a two-dimensional excellent normal local domain $(B,\mathfrak n)$ and an $\mathfrak n$-primary ideal $I$, put
$$
S=\overline{B[It]}=\bigoplus_{n\ge0}\overline{I^n}.
$$
Then $S$ is finite over $B[It]$ and is a normal graded domain. The nonredundant Rees valuation rings of $I$, as in the problem, are precisely the local rings at the generic points of the irreducible components of the reduced exceptional fibre of
$$
\operatorname{Proj}S\to\operatorname{Spec}B.
$$
In particular, $I$ has exactly one Rees valuation ring iff that reduced exceptional fibre is irreducible.

**(V) Standard Veronese generation.** If $S$ is a Noetherian positively graded ring with $S_0$ Noetherian, then some Veronese
$$
S^{(b)}=\bigoplus_{n\ge0}S_{bn}
$$
is generated over $S_0$ by $S_b$. Also $\operatorname{Proj}S^{(b)}\cong\operatorname{Proj}S$; if $S$ is normal, so is $S^{(b)}$.

**(S) Sally’s completion theorem.** Let $(B,\mathfrak n)$ be an analytically irreducible Noetherian local domain. Then $B$ has an $\mathfrak n$-primary ideal with exactly one Rees valuation ring if and only if the integral closure of $\widehat B$ has a zero-dimensional ideal with exactly one Rees valuation ring. This is Sally’s theorem, in the formulation given in Swanson’s survey *Rees Valuations*, Section 3 (Sally, *One-fibered ideals*, MSRI Publications 15, Springer, 1989, p. 440).

In our situation $\widehat A$ will already be a normal local domain, so the integral closure of $\widehat A$ is $\widehat A$ itself, and “zero-dimensional” means primary to its maximal ideal. Thus (S) gives an exact equivalence between the desired property for $A$ and for $\widehat A$.

Finally, we use the standard analytic forms of Zariski’s Main Theorem and surface resolution: between two proper bimeromorphic normal analytic surface germs there is a normalized graph; no curve is contracted by both graph projections; a proper bimeromorphic morphism of normal surfaces with no exceptional curve is an isomorphism; and a morphism to a smooth surface which is an isomorphism away from one closed point is dominated by point blowups over that point, which can be resolved by further point blowups there.

All rings below are excellent and Noetherian, and all analytic blowups are taken over sufficiently small representatives of the relevant germs.

## 2. Explicit elliptic data

Work over $\mathbb C$, and let
$$
E:\qquad Y^2Z=X^3-XZ^2+Z^3.
$$
On $Z=1$ this is
$$
y^2=x^3-x+1.
$$
The discriminant of $x^3-x+1$ is
$$
-4(-1)^3-27(1)^2=-23\ne0,
$$
so $E$ is a smooth elliptic curve. Put
$$
O=(0:1:0),\qquad Q=(0:1:1).
$$
Here $O$ is the identity for the group law. A tangent-line calculation gives
$$
2Q=\left(\frac14,-\frac78\right).
$$
Indeed, the tangent to $y^2=x^3-x+1$ at $(0,1)$ is $y=1-x/2$; substitution gives
$$
x^2\left(x-\frac14\right)=0,
$$
so the third intersection point is $(1/4,7/8)$, and reflection in the $x$-axis gives the displayed formula for $2Q$.

By the Nagell–Lutz theorem for the integral Weierstrass equation $y^2=x^3-x+1$, every rational torsion point has integral coordinates. Since $2Q$ has nonintegral coordinates, $Q$ is non-torsion. Under the standard identification
$$
E(\mathbb C)\simeq\operatorname{Pic}^0(E),\qquad
P\longmapsto\mathcal O_E(P-O),
$$
the class
$$
\mathcal O_E(Q-O)
$$
therefore has infinite order.

Let
$$
C_1=C_2=E,\qquad p_1=p_2=O,
$$
and set
$$
D_1=-[Q],\qquad D_2=-2[Q].
$$
Thus
$$
\deg D_1=-1,\qquad\deg D_2=-2,
$$
and both
$$
\mathcal O_{C_1}(-D_1-p_1)=\mathcal O_E(Q-O),\qquad
\mathcal O_{C_2}(-D_2-2p_2)=\mathcal O_E(2Q-2O)
$$
have infinite order in $\operatorname{Pic}^0(E)$.

## 3. The explicit plumbing and the ring

For a holomorphic line bundle $\mathcal N$ on a curve, $\operatorname{Tot}(\mathcal N)$ will mean the geometric line bundle whose zero section has normal bundle $\mathcal N$. Put
$$
T_1=\operatorname{Tot}\mathcal O_E(D_1)=\operatorname{Tot}\mathcal O_E(-Q),
\qquad
T_2=\operatorname{Tot}\mathcal O_E(D_2)=\operatorname{Tot}\mathcal O_E(-2Q).
$$

The plumbing is made explicit as follows. On the chart $Y\ne0$ of $E$, write
$$
u=X/Y,\qquad w=Z/Y.
$$
Then
$$
w=u^3-uw^2+w^3.
$$
Near the origin $O$, the implicit function theorem gives a unique holomorphic function $\phi(u)$, with $\phi(0)=0$, satisfying
$$
\phi(u)=u^3-u\phi(u)^2+\phi(u)^3.
$$
We use $z=u$ as a local coordinate at $O$. On $E\setminus\{Q\}$, the rational section $1$ trivializes both $\mathcal O_E(D_1)$ and $\mathcal O_E(D_2)$. Choose the same sufficiently small disc $|z|<\varepsilon$ about $O$, small enough that its lift lies in the branch $w=\phi(z)$ and hence avoids the two other points $w=\pm1$ over $z=0$. Let $x_i$ be the fibre coordinate of $T_i$ in this trivialization. Thus $C_i$ is $x_i=0$ near $p_i$.

Glue the two polydiscs by
$$
(z_1,x_1)\longmapsto(z_2,x_2)=(x_1,z_1),
$$
that is, identify $z_1=x_2$ and $x_1=z_2$. This identifies $p_1$ and $p_2$ to one point $p$, and makes the two zero sections meet transversely at $p$. Further shrinking $\varepsilon$ does not change the analytic germ; the displayed coordinate map determines that germ. Let $V$ denote the resulting analytic surface germ around
$$
C=C_1\cup C_2.
$$

The normal bundles are unchanged by this plumbing. Indeed, near $p$, $C_1$ has equation $x_1=0$ in the first chart and $z_2=0$ in the second, and the glue identifies these equations since $x_1=z_2$. Away from $p$, nothing changed. The same argument applies to $C_2$. Consequently
$$
\mathcal O_{C_i}(C_i)\cong\mathcal O_E(D_i).
$$
Therefore
$$
C_1^2=-1,\qquad C_2^2=-2,\qquad C_1\cdot C_2=1.
$$
The intersection matrix is
$$
M=\begin{pmatrix}-1&1\\1&-2\end{pmatrix}.
$$
For $(a,b)\in\mathbb R^2$,
$$
(a,b)M(a,b)^t=-a^2+2ab-2b^2=-(a-b)^2-b^2<0
$$
unless $a=b=0$. Thus $M$ is negative definite.

Grauert’s theorem yields the contraction
$$
g:V\to W
$$
of $C$ to a point $q$, with $W$ normal. Let
$$
A=\mathcal O_{W,q}^{\mathrm{an}}
$$
and define the ring required in the problem by
$$
\boxed{R=\widehat A}
$$
with maximal ideal
$$
\boxed{\mathfrak m=\mathfrak m_A R}.
$$
The analytic germ $W$ is determined by the explicitly plumbed germ $V$; hence $R$ and $\mathfrak m$ are determined by the displayed data $E,Q,O$ and the transition $(z_1,x_1)\mapsto(x_1,z_1)$.

## 4. The elementary ring properties

The analytic local ring $A$ is Noetherian, normal, and two-dimensional. Its completion $R$ is Noetherian and
$$
\widehat R\cong\varprojlim_n R/\mathfrak m^n
\cong\varprojlim_n A/\mathfrak m_A^n=R,
$$
so $R$ is complete in its $\mathfrak m$-adic topology.

By (E), $A$ is excellent and $\widehat A=R$ is normal. Since $R$ is local and normal, it is an integral domain. Also
$$
\dim R=\dim\widehat A=\dim A=2.
$$
Thus $R$ is a two-dimensional complete normal Noetherian local domain. In particular $A$ is analytically irreducible, so Sally’s theorem (S) will apply with $\overline{\widehat A}=\widehat A=R$.

## 5. There are no one-Rees ideals in $A$

We now prove that no $\mathfrak m_A$-primary ideal of the analytic local ring $A$ has exactly one Rees valuation ring.

Suppose otherwise that $I\subset A$ is such an ideal. Let its unique Rees valuation be $v_0$, and put
$$
a=v_0(I)>0.
$$
Since the value ring is a DVR,
$$
IV_0=\mathfrak m_{V_0}^{a}.
$$
For every $n$, the defining property in the question gives
$$
\overline{I^n}=I^nV_0\cap A=\{f\in A:v_0(f)\ge na\}.
$$
Hence
$$
S:=\overline{A[It]}=\bigoplus_{n\ge0}\overline{I^n}
$$
is a normal Noetherian graded domain by (R).

By (V), choose $b>0$ such that $S^{(b)}$ is generated in degree one. Put
$$
J=S_b=\overline{I^b}.
$$
Then
$$
A[Jt]=S^{(b)}
$$
is normal, and
$$
Z_0:=\operatorname{Proj}A[Jt]\cong\operatorname{Proj}S
$$
is the normalized blowup of $I$. Thus its reduced exceptional fibre consists of a single irreducible curve $E$, and $Z_0$ itself is normal. Also $J$ is $\mathfrak m_A$-primary.

Choose a small analytic representative of $(W,q)$ on which the finitely many generators of $J$ are defined, and let
$$
Z=\operatorname{Bl}_J(W)
$$
be the corresponding analytic blowup, shrunk around its exceptional fibre. On each standard chart the analytic local ring has the same completion as the corresponding local ring of the algebraic chart of $Z_0$. Those algebraic local rings are normal because $A$ is excellent and $A[Jt]$ is normal. Their completions are therefore normal, and normality descends from a faithfully flat completion to a local domain. Hence $Z$ is normal. Its reduced exceptional fibre is the same curve $E$.

Let
$$
\alpha=v_E(J)>0.
$$
On $Z$ the invertible ideal $J\mathcal O_Z=\mathcal O_Z(1)$ has support $E$, so
$$
J\mathcal O_Z=\mathcal O_Z(-\alpha E),
\qquad \alpha E\ \text{is Cartier}.
\tag{5.1}
$$
Moreover $\mathcal O_Z(1)=\mathcal O_Z(-\alpha E)$ is relatively very ample for $Z\to W$.

Consequently, if $h:Y\to Z$ is a proper bimeromorphic morphism from a smooth analytic surface and $B\subset Y$ is a compact curve contracted by $h$, then
$$
\mathcal O_B\otimes h^*\mathcal O_Z(-\alpha E)\cong\mathcal O_B.
\tag{5.2}
$$
Indeed, the relatively very ample sheaf embeds $Z$ into projective space over the germ $W$; the induced map sends $B$ to one point, so the pullback of $\mathcal O(1)$ to $B$ is trivial. In particular
$$
\deg\bigl(h^*\mathcal O_Z(-\alpha E)|_B\bigr)=0.
\tag{5.3}
$$

Let $\Gamma$ be the normalization of the closure of the graph of the bimeromorphic map between the fixed plumbing $V$ and $Z$. No curve of $\Gamma$ is contracted by both projections $\Gamma\to V$ and $\Gamma\to Z$, because its image in $V\times_WZ$ would then be one point. If $F$ is contracted by $\Gamma\to V$ but not by $\Gamma\to Z$, then $F$ maps onto $E$; the valuation of its generic point is therefore $v_0$, and its image on $V$ is the center of $v_0$. This graph observation and Zariski’s Main Theorem will be used in each case.

The center of $v_0$ on $V$ is either $C_1$, $C_2$, or a closed point of $C_1\cup C_2$.

In the following computations it is convenient to recall
$$
D_1=-Q,\qquad D_2=-2Q,\qquad p_1=p_2=O.
$$

### 5.1 Center $C_1$

A curve exceptional for $\Gamma\to V$ would have center a closed point on $V$, contradicting that the center is $C_1$. Thus $\Gamma\to V$ has no exceptional curve, and Zariski’s Main Theorem gives a morphism
$$
h:V\to Z.
$$
The curve $C_1$, and not $C_2$, maps onto $E$. Thus $h$ contracts $C_2$. Since the generic local rings of $E$ and $C_1$ are both the same valuation ring, the pullback of $E$ has coefficient $1$ on $C_1$. Write
$$
L:=h^*\mathcal O_Z(-\alpha E)=-\alpha C_1-sC_2,\qquad s>0.
$$
Using $L|_{C_2}\cong\mathcal O_{C_2}$ and (5.3),
$$
0=L\cdot C_2=-\alpha+2s,
$$
so $\alpha=2s$. Hence
$$
\begin{aligned}
\mathcal O_{C_2}(L)
&\cong\mathcal O_E\bigl(-\alpha p_2-sD_2\bigr)\\
&\cong\mathcal O_E\bigl(-2sO+2sQ\bigr)\\
&\cong\mathcal O_E\bigl(s(2Q-2O)\bigr).
\end{aligned}
$$
This is nontrivial because $2Q-2O=2(Q-O)$ has infinite order and $s>0$. This contradicts (5.2).

### 5.2 Center $C_2$

Symmetrically, Zariski’s Main Theorem gives $h:V\to Z$, now contracting $C_1$. Write
$$
L=-tC_1-\alpha C_2,\qquad t>0.
$$
From $L|_{C_1}\cong\mathcal O_{C_1}$,
$$
0=L\cdot C_1=t-\alpha,
$$
so $t=\alpha$. Therefore
$$
\begin{aligned}
\mathcal O_{C_1}(L)
&\cong\mathcal O_E\bigl(-\alpha D_1-\alpha p_1\bigr)\\
&\cong\mathcal O_E\bigl(\alpha(Q-O)\bigr),
\end{aligned}
$$
which is nontrivial because $Q-O$ has infinite order and $\alpha>0$, again contradicting (5.2).

### 5.3 Center $p=C_1\cap C_2$

The graph observation shows that every curve exceptional for $\Gamma\to V$ lies over $p$. Resolution of the normalized graph gives a smooth analytic surface and morphisms
$$
Y\xrightarrow{g}V,\qquad Y\xrightarrow{h}Z,
$$
where $g$ is a product of blowups at $p$ and at points infinitely near to $p$. Let $B_1,B_2$ be the proper transforms of $C_1,C_2$, and let $B_3,\dots,B_r$ be the other exceptional curves. Exactly one exceptional curve meets $B_1$; call it $B_3$, and its intersection with $B_1$ corresponds to $p_1=O$. All other $B_i$ are disjoint from $B_1$.

The center of $v_0$ lies over $p$, so it is not the generic point of $B_1$; hence $h$ contracts $B_1$. Write
$$
L:=h^*\mathcal O_Z(-\alpha E)=-\mu B_1-\nu B_3-F,
\tag{5.4}
$$
where $\mu,\nu>0$ and $\operatorname{Supp}F\cap B_1=\varnothing$. Positivity holds because $J$ is $\mathfrak m_A$-primary and every exceptional component defines a divisorial valuation centered at $\mathfrak m_A$, so its value on $J$ is strictly positive.

We need the effect of the point blowups on the normal bundle of $B_1$. If $C$ is a smooth curve on a smooth surface $Y'$ with
$$
\mathcal O_C(C)\cong\mathcal O_C(D)
$$
and $q\in C$, then blowing up $q$, writing $F$ for the exceptional curve and $C'$ for the proper transform, gives $f^*C=C'+F$. Restricting to $C'$ yields
$$
\mathcal O_{C'}(C')\otimes\mathcal O_{C'}(F)
\cong\mathcal O_C(D),
\qquad
\mathcal O_{C'}(F)\cong\mathcal O_C(q),
$$
and hence
$$
\mathcal O_{C'}(C')\cong\mathcal O_C(D-q).
\tag{5.5}
$$
Iterating (5.5), for some integer $c>0$,
$$
\mathcal O_{B_1}(B_1)\cong\mathcal O_E(D_1-cO).
$$
Thus
$$
B_1^2=\deg(D_1)-c=-1-c.
$$
Since $h$ contracts $B_1$, (5.3) gives
$$
0=L\cdot B_1
=-\mu B_1^2-\nu B_3\cdot B_1
=\mu(1+c)-\nu.
$$
Hence
$$
\nu=\mu(1+c).
\tag{5.6}
$$
Restricting (5.4) to $B_1$ and using (5.6),
$$
\begin{aligned}
\mathcal O_{B_1}(L)
&\cong\mathcal O_E\bigl(-\mu(D_1-cO)-\nu O\bigr)\\
&\cong\mathcal O_E\bigl(-\mu D_1+\mu cO-\mu(1+c)O\bigr)\\
&\cong\mathcal O_E\bigl(\mu(-D_1-O)\bigr)\\
&\cong\mathcal O_E\bigl(\mu(Q-O)\bigr).
\end{aligned}
$$
This is nontrivial because $\mu>0$ and $Q-O$ has infinite order, contradicting (5.2).

### 5.4 Center a point of $C_1\setminus C_2$

Let the center be $q\in C_1\setminus C_2$. As above, the graph has no exceptional curve except over $q$. Resolve it by point blowups over $q$:
$$
Y\xrightarrow{g}V,\qquad Y\xrightarrow{h}Z.
$$
Let $B_1$ be the proper transform of $C_1$. The proper transform of $C_2$ is unchanged; denote it again by $C_2$. Every curve exceptional for $g$ lies over $q$, so is disjoint from $C_2$.

The center is not $C_2$, so $h$ contracts $C_2$. Write
$$
L=-\mu C_2-\lambda B_1-F,\qquad \mu,\lambda>0,
$$
with $\operatorname{Supp}F\cap C_2=\varnothing$. Since $C_2^2=-2$ and $C_2\cdot B_1=1$, (5.3) gives
$$
0=L\cdot C_2=2\mu-\lambda.
$$
Thus $\lambda=2\mu$. Hence
$$
\begin{aligned}
\mathcal O_{C_2}(L)
&\cong\mathcal O_E\bigl(-\mu D_2-\lambda O\bigr)\\
&\cong\mathcal O_E\bigl(2\mu Q-2\mu O\bigr)\\
&\cong\mathcal O_E\bigl(\mu(2Q-2O)\bigr),
\end{aligned}
$$
which is nontrivial. This contradicts (5.2).

### 5.5 Center a point of $C_2\setminus C_1$

This is symmetric to §5.4. Let $B_2$ be the proper transform of $C_2$. Now $C_1$ is unchanged and is contracted by $h$. Write
$$
L=-\mu C_1-\lambda B_2-F,\qquad \mu,\lambda>0,
$$
with $\operatorname{Supp}F\cap C_1=\varnothing$. Since $C_1^2=-1$ and $C_1\cdot B_2=1$,
$$
0=L\cdot C_1=\mu-\lambda,
$$
so $\lambda=\mu$. Therefore
$$
\begin{aligned}
\mathcal O_{C_1}(L)
&\cong\mathcal O_E\bigl(-\mu D_1-\lambda O\bigr)\\
&\cong\mathcal O_E\bigl(\mu Q-\mu O\bigr)\\
&\cong\mathcal O_E\bigl(\mu(Q-O)\bigr),
\end{aligned}
$$
nontrivial. Contradiction.

All possible centers are exhausted. Hence $A$ has no $\mathfrak m_A$-primary ideal with exactly one Rees valuation ring.

## 6. Passage to the completion and conclusion

By §4,
$$
\widehat A=R
$$
is a normal local domain. Thus $A$ is analytically irreducible and
$$
\overline{\widehat A}=\widehat A=R.
$$
Apply Sally’s theorem (S) to $B=A$. Since $A$ has no $\mathfrak m_A$-primary one-Rees ideal and $\overline{\widehat A}=R$, the completed ring $R$ has no zero-dimensional one-Rees ideal. As $R$ is local and two-dimensional, the zero-dimensional ideals in question are exactly the $\mathfrak m$-primary ideals. Therefore no $\mathfrak m$-primary ideal of $R$ has exactly one Rees valuation ring.

For every nonzero proper ideal, Rees’s existence theorem supplies at least one Rees valuation ring. Hence every $\mathfrak m$-primary ideal of $R$ has at least two.

The desired example is therefore explicitly
$$
\boxed{
(R,\mathfrak m)=
\left(
\widehat{\mathcal O_{W,q}^{\mathrm{an}}},
\;
\mathfrak m_{W,q}\,\widehat{\mathcal O_{W,q}^{\mathrm{an}}}
\right),
}
$$
where $W$ is the Grauert contraction of the plumbing of
$$
\operatorname{Tot}\mathcal O_E(-Q)
\quad\text{and}\quad
\operatorname{Tot}\mathcal O_E(-2Q)
$$
along $O\in E$, glued in local coordinates by
$$
(z_1,x_1)\sim(z_2,x_2)\quad\Longleftrightarrow\quad z_1=x_2,\ x_1=z_2,
$$
with
$$
E:\ y^2=x^3-x+1,\qquad O=(0:1:0),\qquad Q=(0:1:1).
$$
This $R$ is a two-dimensional complete normal Noetherian local domain, and every $\mathfrak m$-primary ideal in $R$ has at least two Rees valuation rings.
