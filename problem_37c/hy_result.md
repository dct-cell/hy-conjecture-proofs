# A counterexample to Problem 37(c)

We construct a field $A$, a domain $D$, a prime $P\in\operatorname{Spec}D$, and an affine $A$-domain $T$ such that
$$
A\subseteq D\subseteq T,
$$
while $D_P$ has finite Krull dimension two but
$$
\dim D_P[X]\ge 4>3=\dim D_P+1.
$$
Thus $D_P$ is not Jaffard and $D$ is not locally Jaffard.

The construction is a streamlined form of the digit-coded lift in Tran–Vo–Nguyen, *Bouvier’s conjecture is true* [1, §§3–5]. We do **not** need their stronger conclusions that the rings are UFDs or that the global ring is Jaffard. In particular, this proof does not rely on their polynomial upper bound for Krull domains.

## 1. Valuation facts used

We use the following standard results in these exact forms.

1. **Domination theorem.** If $(S,\mathfrak m)$ is a local domain with fraction field $F$, there is a valuation ring $V\subseteq F$ containing $S$ such that $\mathfrak m_V\cap S=\mathfrak m$ [2, Lemma 10.50.2].

2. **Zariski–Abhyankar inequality** [3, Lemma 6.31]. If $L/k$ is a finitely generated field extension and $w$ is a valuation on $L$, trivial on $k$, with value group $\Gamma_w$ and residue field $\kappa(w)$, then
   $$
   \operatorname{ratrank}\Gamma_w+\operatorname{trdeg}_k\kappa(w)
   \le \operatorname{trdeg}_k L.
   $$

3. **Finite-extension inequality** [4, Theorem 7.49]. If $L/K$ is a finite field extension and $w$ on $L$ restricts to $v$ on $K$, then
   $$
   [\Gamma_w:\Gamma_v]<\infty,\qquad
   [\kappa(w):\kappa(v)]<\infty,
   $$
   and, for this single extension,
   $$
   [\Gamma_w:\Gamma_v]\,[\kappa(w):\kappa(v)]\le [L:K].
   $$

4. The prime ideals of a valuation domain correspond to the convex subgroups of its value group. Consequently the rank of a valuation domain is the rank of its value group, which is at most its rational rank [5, Propositions 6.6.4 and 6.6.6].

We shall also use, without further comment, the usual prime correspondence under localization.

## 2. The boundary domain

Let
$$
\Bbbk=\overline{\mathbf F}_2,\qquad
K_\partial=\bigcup_{r\ge0}\Bbbk\bigl(t^{1/2^r}\bigr),\qquad
\Gamma=\mathbf Z[1/2],
$$
where $t$ is transcendental over $\Bbbk$. Write $\chi^\gamma$ for the group-ring element of exponent $\gamma$, and put
$$
\mathcal L=\operatorname{Frac}\bigl(K_\partial[\Gamma]\bigr).
$$
The rule
$$
v\!\left(\sum_{\gamma}c_\gamma\chi^\gamma\right)
 =\min\{\gamma:c_\gamma\ne0\}
$$
defines a valuation on $\mathcal L$. Its value group is $\Gamma$, and its residue field is $K_\partial$. Let
$$
V=\{z:v(z)\ge0\},\qquad M=\{z:v(z)>0\}.
$$
Set
$$
N=\bigoplus_{\gamma>0}K_\partial\chi^\gamma,\qquad
E=\Bbbk\oplus N\subseteq K_\partial[\Gamma],
$$
and let
$$
B=E_N.
$$

Since $\Bbbk$ and $K_\partial$ are countable, so is $E$. All choices below are made from fixed enumerations of the relevant countable sets; when a finite set is to be avoided and an allowable choice exists, we take the first one in the fixed enumeration. This makes the rings and digits below explicitly determined.

### Lemma 2.1

One has
$$
B=\Bbbk+M.
$$
Hence $B$ is local with maximal ideal $M$, and its complete prime spectrum is
$$
(0)\subsetneq M.
$$
In particular $\dim B=1$. Moreover
$$
\operatorname{Frac}B=\mathcal L
\quad\text{and}\quad
\operatorname{trdeg}_{\Bbbk}\mathcal L=2.
$$

### Proof

First consider $e/s\in B$, with $e=c+n\in E$, $s=d+m\in E\setminus N$, $c,d\in\Bbbk$, $n,m\in N$, $d\ne0$. Both $e,s\in V$, $v(s)=0$, and
$$
\operatorname{res}_v(e/s)=c/d\in\Bbbk.
$$
Thus $e/s-c/d\in M$, giving $B\subseteq\Bbbk+M$.

Conversely, let $0\ne z\in M$. Write $z=f/g$ with $f,g\in K_\partial[\Gamma]$. Let $c\chi^\beta$ be the least term of $g$. Dividing numerator and denominator by this term gives
$$
z=\frac{f'}{1+h},\qquad h\in N.
$$
Since $v(z)>0$, every exponent in $f'$ is positive, so $f'\in N$, while $1+h\in E\setminus N$. Hence $M\subseteq B$. If $c\in\Bbbk^\times$ and $m\in M$, then $c+m$ has inverse in $V$ with residue $c^{-1}$, so its inverse belongs to $c^{-1}+M\subseteq B$. No element of $M$ is invertible in $B$, because $B\subseteq V$. Thus $B$ is local with maximal ideal $M$.

If $\mathfrak p\ne0$ is prime in $B$ and $0\ne a\in\mathfrak p$, then $a\in M$. For $0\ne b\in M$, the ordered group $\Gamma\subseteq\mathbf R$ is Archimedean, so choose $n$ with $nv(b)>v(a)$. Then
$$
b^n/a\in M\subseteq B,\qquad b^n=a(b^n/a)\in\mathfrak p,
$$
and primality gives $b\in\mathfrak p$. Hence $\mathfrak p=M$.

Every positive monomial $c\chi^\gamma$ lies in $N$, and so $E\subseteq\mathcal L$ and $\operatorname{Frac}E\subseteq\mathcal L$. Conversely,
$$
c=\frac{c\chi}{\chi},\qquad
\chi^\gamma=\frac{\chi^{\gamma+m}}{\chi^m}
$$
for an integer $m$ with $\gamma+m>0$ show that every $c\in K_\partial$ and every $\chi^\gamma$ lies in $\operatorname{Frac}E$. Thus $\operatorname{Frac}B=\operatorname{Frac}E=\mathcal L$. Finally
$$
t=\frac{t\chi}{\chi}\in\operatorname{Frac}B.
$$
The elements $t,\chi$ are algebraically independent over $\Bbbk$; $K_\partial/\Bbbk(t)$ is algebraic and every $\chi^{a/2^r}$ is algebraic over $\Bbbk(\chi)$. Thus $\operatorname{trdeg}_{\Bbbk}\mathcal L=2$. $\square$

### Lemma 2.2

Let $X$ be an indeterminate. Then $B[X]$ contains a chain of four distinct primes
$$
(0)\subsetneq Q_B\subsetneq M[X]\subsetneq(M,X).
$$
Consequently $\dim B[X]\ge3$.

### Proof

Multiplication by $t$ does not change $v$, so $tM\subseteq M$. Choose $0\ne a\in M$. Evaluation
$$
\varepsilon:B[X]\longrightarrow\mathcal L,\qquad X\longmapsto t
$$
has prime kernel $Q_B$. It is nonzero because
$$
aX-ta\in Q_B.
$$
We claim $Q_B\subseteq M[X]$. Write
$$
f=\sum_i(c_i+m_i)X^i\in Q_B,\qquad c_i\in\Bbbk,\ m_i\in M.
$$
Then
$$
0=f(t)=\sum_i c_it^i+\sum_i m_it^i.
$$
The first sum belongs to $K_\partial$ and has value $0$ if nonzero. The second has positive value if nonzero. They cannot cancel. Since $t$ is transcendental over $\Bbbk$, every $c_i=0$, so $f\in M[X]$. The inclusion is strict because $0\ne a\in M[X]\setminus Q_B$. Finally, $M[X]$ and $(M,X)$ are prime, with quotients $\Bbbk[X]$ and $\Bbbk$, and $X\notin M[X]$. This proves the displayed chain. $\square$

## 3. Exhausting $E$ by polynomial planes

We now make the limiting algebra explicit.

Call $s\in K_\partial$ an **admissible coordinate** if $\Bbbk(s)=\Bbbk(t^{1/2^q})$ for some $q\ge0$. For $a\in K_\partial^\times$, such an $s$, and $0<\delta\in\Gamma$, define
$$
P(a,s,\delta)
 =\Bbbk[a\chi^\delta,\,as\chi^\delta]\subseteq E.
$$
Its two generators are algebraically independent: terms of different total degree have different $v$-values, and a homogeneous relation reduces to a polynomial relation in $s$ over $\Bbbk$. Thus $P(a,s,\delta)$ is a polynomial plane. We call $\delta$ dyadically normalized when $\delta=2^{-e}$.

There are two elementary enlargements.

**Frobenius enlargement.** Since $\operatorname{char}\Bbbk=2$ and $\Bbbk$ is perfect, $K_\partial$ is perfect. Put
$$
A_0=a^{1/2}\chi^{\delta/2},\qquad
B_0=a^{1/2}s^{1/2}\chi^{\delta/2}.
$$
Then the old generators are $A_0^2,B_0^2$. After interchanging the two old generators, the inclusion is therefore
$$
\text{old coordinates}=(B_0^2,A_0^2).
$$

**Binary enlargement.** Let $L(S)=\ell_0+\ell_1S$ and $H(S)=h_0+h_1S$ be linearly independent over $\Bbbk$. Change the old generators to
$$
C=aL(s)\chi^\delta,\qquad D=aH(s)\chi^\delta.
$$
Put
$$
A_0=(aL(s))^{1/2}\chi^{\delta/2},\qquad
B_0=(aL(s))^{1/2}\frac{H(s)}{L(s)}\chi^{\delta/2}.
$$
Then
$$
C=A_0^2,\qquad D=A_0B_0.
$$
After interchanging the old generators the inclusion is
$$
\text{old coordinates}=(A_0B_0,A_0^2).
$$
Both elementary maps are injective, because the exponent pairs of distinct monomials in $A_0^2,A_0B_0$, respectively in $A_0^2,B_0^2$, are distinct.

### Lemma 3.1

Let $P(a,s,\delta)$ be dyadically normalized, and let
$$
f_i\chi^{\gamma_i}\quad(1\le i\le r)
$$
be finitely many nonconstant monomial terms of $E$. A finite sequence of Frobenius and binary enlargements produces a plane containing all these terms.

### Proof

First apply Frobenius enlargements until every $m_i=\gamma_i/\delta$ is a positive integer. Further Frobenius enlargements replace
$$
a\mapsto a^{1/2^u},\quad s\mapsto s^{1/2^u},\quad
\delta\mapsto\delta/2^u,\quad m_i\mapsto2^um_i,
$$
so $a^{m_i}$ remains unchanged after the corresponding powers are taken. Since
$$
K_\partial=\bigcup_{u\ge0}\Bbbk(s^{1/2^u}),
$$
we may arrange
$$
q_i:=f_i/a^{m_i}\in\Bbbk(s)^\times\quad\text{for all }i.
$$

We now describe the binary step. Let $P_j$ denote the pole of the coordinate after the $j$-th binary enlargement. We may prescribe these poles subject to the harmless convention that $L_j=1$ if $P_{j+1}=P_j$; otherwise take a linear polynomial with
$$
\operatorname{div}(L_j)=P_{j+1}-P_j.
$$
Choosing a second independent linear polynomial and dividing gives the next coordinate, whose pole is $P_{j+1}$. If $a_j$ is the $j$-th carrier, then $a_{j+1}^2=a_jL_j$, and
$$
a_n^{2^n}=a\prod_{j=0}^{n-1}L_j^{2^j},\qquad
\delta_n=\delta/2^n.
$$
For the $i$-th target, its degree in the final frame is $d_i=m_i2^n$, and
$$
g_{i,n}:=\frac{f_i}{a_n^{d_i}}
 =q_i\prod_{j=0}^{n-1}L_j^{-m_i2^j}.
$$
The weighted divisor telescopes:
$$
\sum_{j=0}^{n-1}2^j(P_{j+1}-P_j)
=-P_0-\sum_{j=1}^{n-1}2^{j-1}P_j+2^{n-1}P_n.
$$
Let $\Sigma$ be the union of the pole supports of the finitely many divisors $\operatorname{div}(q_i)$. For each $R\in\Sigma$, choose distinct positive integers $j(R)$, sufficiently large that
$$
m_i2^{j(R)-1}\ge-\operatorname{ord}_R(q_i)
$$
for every $i$. Prescribe $P_{j(R)}=R$. At all other intermediate stages choose points outside all supports; then choose a fresh $P_n$ outside all supports and distinct from the preceding points. If $\Sigma=\varnothing$, take $n=1$ and choose $P_1$ fresh. Since $\Bbbk$ is infinite, all these choices exist.

It follows that the only possible pole of $g_{i,n}$ is the fresh point $P_n$, where
$$
\operatorname{ord}_{P_n}(g_{i,n})=-m_i2^{n-1}.
$$
The final coordinate $s_n$ has its unique simple pole at $P_n$. Hence a rational function on $\mathbf P^1_\Bbbk$ with only that pole and order at most $d$ is a polynomial in $s_n$ of degree at most $d$. Therefore
$$
g_{i,n}\in\Bbbk[s_n],\qquad
\deg_{s_n}g_{i,n}=m_i2^{n-1}\le d_i.
$$
Writing $g_{i,n}(S)=\sum_{j=0}^{d_i}c_{ij}S^j$, and setting
$$
U_n=a_n\chi^{\delta_n},\qquad V_n=a_ns_n\chi^{\delta_n},
$$
we obtain
$$
\sum_{j=0}^{d_i}c_{ij}U_n^{d_i-j}V_n^j
=a_n^{d_i}\chi^{d_i\delta_n}g_{i,n}(s_n)
=f_i\chi^{\gamma_i}.
$$
Thus the final plane contains every target. $\square$

Now enumerate all nonconstant monomial terms of $E$ as $h_1,h_2,\ldots$. Start with
$$
P_0=P(1,t,1)=\Bbbk[\chi,t\chi].
$$
Given $P_n$, apply Lemma 3.1 to $P_n$ and $h_{n+1}$, and insert every intermediate plane into the sequence. This gives an explicitly indexed chain
$$
P_0\subset P_1\subset\cdots\subset E,\qquad
\bigcup_{n\ge0}P_n=E.
$$
Write $P_n=\Bbbk[x_n,y_n]$. By construction, for each $n$ there is a matrix $M_n\in\operatorname{GL}_2(\Bbbk)$ such that, with
$$
\binom{u_n}{v_n}=M_n\binom{x_n}{y_n},
$$
the inclusion $P_n\subseteq P_{n+1}$ has one of the two forms
$$
u_n=F_n(x_{n+1},y_{n+1}),\qquad v_n=x_{n+1}^2,
$$
where
$$
F_n(R,S)\in\{RS,S^2\}.
\tag{3.1}
$$
The matrix $M_n$ is chosen independently for each arrow; it is not identified with the incoming target frame of the preceding arrow. All these choices are made using the fixed enumeration of $\Bbbk$.

## 4. The digit-coded lift

Let
$$
\mathcal O=\Bbbk[[\pi]],\qquad \mathfrak m=\pi\mathcal O,
$$
where $\pi$ is a new indeterminate. For
$$
d=((\alpha_n,\beta_n,\gamma_n))_{n\ge0}\in(\Bbbk^3)^{\mathbf N}
$$
we define backward state maps $\Phi_n:\mathfrak m^3\to\mathfrak m^3$. If the stored state at level $n+1$ is $(X_{n+1},Y_{n+1},Z_{n+1})$, put first
$$
\begin{aligned}
U&=F_n(X_{n+1},Y_{n+1})+\pi(Z_{n+1}+\alpha_n),\\
V&=X_{n+1}^2+\pi(Y_{n+1}+\beta_n),\\
W&=\pi(X_{n+1}+\gamma_n),
\end{aligned}
\tag{4.1}
$$
and then set
$$
\binom{X_n}{Y_n}=M_n^{-1}\binom{U}{V},\qquad Z_n=W.
$$
Thus $\Phi_n(X_{n+1},Y_{n+1},Z_{n+1})=(X_n,Y_n,Z_n)$.

For vectors in $\mathfrak m^3$, write
$$
\operatorname{ord}(q)=\min_i\operatorname{ord}_\pi(q_i),\qquad
\operatorname{ord}_\pi(0)=+\infty.
$$

### Lemma 4.1

For all $q,q'\in\mathfrak m^3$,
$$
\operatorname{ord}\bigl(\Phi_n(q)-\Phi_n(q')\bigr)
\ge \operatorname{ord}(q-q')+1.
\tag{4.2}
$$

### Proof

An invertible matrix over $\Bbbk$, and its inverse, preserve the minimum of the two orders. In the displayed target frame it therefore suffices to inspect (4.1). The constants cancel. If the next-state coordinates have difference of order at least $r$, then
$$
AB-A'B'=A(B-B')+B'(A-A'),
$$
and, in characteristic two,
$$
A^2-A'^2=(A-A')^2,\qquad B^2-B'^2=(B-B')^2.
$$
Each displayed term gains at least one order. Every remaining tail is multiplied by $\pi$. Taking the minimum proves (4.2). $\square$

Consequently, for every digit sequence $d$, there is a unique compatible sequence of stored states
$$
q_n(d)=(\xi_n,\eta_n,\zeta_n)\in\mathfrak m^3,\qquad
q_n(d)=\Phi_n(q_{n+1}(d)).
\tag{4.3}
$$
Indeed, truncate the digits at level $N$, set $q_N=0$, and use $\Phi_{N-1}\circ\cdots\circ\Phi_n$. By (4.2), these approximants are Cauchy; completeness of $\mathcal O$ gives $q_n$. Two compatible sequences differ by at least order $N-n+1$, so uniqueness follows.

Conversely, a stored state at level $n$ determines the next digit and next state. If
$$
(U_n,V_n)^t=M_n(X_n,Y_n)^t,
$$
then define successively
$$
\begin{aligned}
\gamma_n&=\operatorname{ct}(Z_n/\pi),&
X_{n+1}&=Z_n/\pi-\gamma_n,\\
\beta_n&=\operatorname{ct}\bigl((V_n-X_{n+1}^2)/\pi\bigr),&
Y_{n+1}&=\bigl(V_n-X_{n+1}^2\bigr)/\pi-\beta_n,\\
\alpha_n&=\operatorname{ct}\bigl((U_n-F_n(X_{n+1},Y_{n+1}))/\pi\bigr),&
Z_{n+1}&=\bigl(U_n-F_n(X_{n+1},Y_{n+1})\bigr)/\pi-\alpha_n.
\end{aligned}
\tag{4.4}
$$
Here $\operatorname{ct}$ denotes the constant term. These formulas show that the map $q_0\mapsto d$ is a bijection $\mathfrak m^3\to(\Bbbk^3)^{\mathbf N}$, inverse to $d\mapsto q_0(d)$. Moreover, if two digit sequences agree through level $N-1$, their level-zero states agree modulo $\pi^{N+1}$; this is immediate from (4.2).

We need a code with $\gamma_n\ne0$ for every $n$ and with $q_0(d)$ algebraically independent over $\Bbbk(\pi)$. Such a code can be chosen explicitly by diagonalization. Put
$$
\mathcal C=(\Bbbk^2\times\Bbbk^\times)^{\mathbf N}.
$$
Fix an enumeration
$$
H_1,H_2,\ldots
$$
of the nonzero polynomials in $\Bbbk(\pi)[X,Y,Z]$.

Suppose a finite initial digit prefix has already been fixed, say through level $N-1$, where $N$ is the first free level. Fix all digits after $N$ to be $(0,0,1)$, thus fixing a state $q_{N+1}$. Leaving only $(\alpha_N,\beta_N,\gamma_N)$ free, equations (4.1) express $q_N$ as an affine function of these three digits whose linear part is $\pi$ times an invertible matrix. The earlier fixed-digit maps are polynomial automorphisms over the field generated by $\Bbbk(\pi)$ and the coordinates of $q_{N+1}$, as is clear from the inverse formulas (4.4) after inverting $\pi$. Therefore
$$
(\alpha_N,\beta_N,\gamma_N)\longmapsto H_j(q_0)
$$
is either zero or a nonzero polynomial over that field. Since $H_j\ne0$ and the maps are automorphisms, it is nonzero. Because $\Bbbk$ is infinite, $\Bbbk^2\times\Bbbk^\times$ is Zariski dense, so choose $(\alpha_N,\beta_N,\gamma_N)\in\Bbbk^2\times\Bbbk^\times$ where its value is nonzero.

Now multiply $H_j$ by a common denominator $h(\pi)\in\Bbbk[\pi]\setminus\{0\}$, obtaining
$$
G=hH_j\in\Bbbk[\pi,X,Y,Z].
$$
For the resulting code, $G(q_0)$ is a nonzero element of $\mathcal O$. Let $\pi^r$ be its initial term. Freeze sufficiently many additional digits that any code with this finite prefix has level-zero state congruent to $q_0$ modulo $\pi^{r+1}$. Then $G(q_0)$ remains nonzero for every code in the resulting cylinder. Proceed to $H_{j+1}$. The union of the resulting increasing finite prefixes is a well-defined digit string $d\in\mathcal C$, selected by the fixed enumerations, and no $H_j$ vanishes at $q_0(d)$. Thus
$$
\gamma_n\ne0\quad(n\ge0),\qquad
\xi_0,\eta_0,\zeta_0\ \text{are algebraically independent over }\Bbbk(\pi).
\tag{4.5}
$$
Fix this $d$ and its compatible states $q_n=(\xi_n,\eta_n,\zeta_n)$.

For every $n$, define
$$
S_n=\Bbbk[\pi,x_n,y_n,z_n],
$$
and define a $\Bbbk[\pi]$-homomorphism
$$
\iota_n:S_n\longrightarrow S_{n+1}
$$
by the equations
$$
\boxed{
\begin{aligned}
u_n&=F_n(x_{n+1},y_{n+1})+\pi(z_{n+1}+\alpha_n),\\
v_n&=x_{n+1}^2+\pi(y_{n+1}+\beta_n),\\
z_n&=\pi(x_{n+1}+\gamma_n),
\end{aligned}}
\tag{4.6}
$$
where $(u_n,v_n)^t=M_n(x_n,y_n)^t$. These equations determine the images of $x_n,y_n,z_n$, because $M_n$ is invertible.

After inverting $\pi$, equations (4.6) have the successive inverse
$$
\begin{aligned}
x_{n+1}&=z_n/\pi-\gamma_n,\\
y_{n+1}&=(v_n-x_{n+1}^2)/\pi-\beta_n,\\
z_{n+1}&=(u_n-F_n(x_{n+1},y_{n+1}))/\pi-\alpha_n.
\end{aligned}
\tag{4.7}
$$
Thus $\iota_n[1/\pi]$ is an isomorphism. Since $S_n$ is a domain and $\pi$-torsion-free, $\iota_n$ is injective.

Using these generic identifications, realize all $S_n$ as nested subrings of
$$
T:=S_0[1/\pi]
 =\Bbbk[\pi,\pi^{-1},x_0,y_0,z_0].
\tag{4.8}
$$
More precisely, start with the identity embedding of $S_0$, and use the inverse formulas in (4.7) to embed $S_{n+1}$, given $S_n$. Then $\iota_n$ becomes an inclusion. Put
$$
R=\bigcup_{n\ge0}S_n\subseteq T.
\tag{4.9}
$$
By construction,
$$
R[1/\pi]=S_0[1/\pi]=T.
\tag{4.10}
$$

### Lemma 4.2

There is a canonical isomorphism
$$
R/\pi R\simeq E.
$$

### Proof

Filtered colimits commute with quotient by the element $\pi$ from the base, so
$$
R/\pi R\simeq\varinjlim_n(S_n/\pi S_n).
$$
Let
$$
\overline S_n=\Bbbk[x_n,y_n,z_n].
$$
Reduction of (4.6) gives
$$
u_n\longmapsto F_n(x_{n+1},y_{n+1}),\qquad
v_n\longmapsto x_{n+1}^2,\qquad z_n\longmapsto0.
\tag{4.11}
$$
Restricted to $P_n=\Bbbk[x_n,y_n]$, this is precisely the $n$-th plane arrow (3.1). Every element of $\overline S_n$ enters the plane subring $P_{n+1}$ after one transition, because $z_n$ is killed. Hence
$$
\varinjlim P_n\longrightarrow\varinjlim\overline S_n
$$
is surjective. It is injective: if an element of $P_n$ becomes zero in some later $\overline S_m$, then it is already zero in $P_m$, and all plane arrows are injective. Therefore
$$
R/\pi R\simeq\varinjlim_nP_n=E. \qquad\square
$$

Let
$$
P=\{r\in R:\overline r\in N\},
\tag{4.12}
$$
where $\overline r$ denotes its image in $E$. Then
$$
R/P\simeq E/N\simeq\Bbbk,
$$
so $P$ is a maximal, hence prime, ideal.

For $f\in S_n$, push it one step into $S_{n+1}$ and compute its special fibre using (4.11). Writing $f$ in the outgoing frame $(u_n,v_n,z_n)$, its image is
$$
f\bigl(F_n(x_{n+1},y_{n+1}),x_{n+1}^2,0\bigr).
$$
Its constant part in $E$ is precisely the constant term of $f$. Hence
$$
P\cap S_n=\mathfrak m_n:=(\pi,x_n,y_n,z_n).
\tag{4.13}
$$

The substitutions
$$
\pi\longmapsto\pi,\qquad x_n\longmapsto\xi_n,\qquad
y_n\longmapsto\eta_n,\qquad z_n\longmapsto\zeta_n
$$
are compatible with all $\iota_n$, by (4.3), and therefore induce
$$
\operatorname{ev}:R\longrightarrow\mathcal O=\Bbbk[[\pi]].
\tag{4.14}
$$
After inverting $\pi$, under the identification $R[1/\pi]=T$, this is substitution of the algebraically independent triple $(\xi_0,\eta_0,\zeta_0)$ over $\Bbbk(\pi)$. Hence $\operatorname{ev}$ is injective.

If $s\in R\setminus P$, choose $n$ with $s\in S_n$. By (4.13), $s\notin\mathfrak m_n$, so its constant term is nonzero. Since every $\xi_n,\eta_n,\zeta_n$ lies in $\mathfrak m$, the constant term of $\operatorname{ev}(s)$ is that same nonzero element of $\Bbbk$. Thus $\operatorname{ev}(s)$ is a unit of $\mathcal O$. Consequently (4.14) extends to an injective map
$$
\operatorname{ev}_P:R_P\longrightarrow\mathcal O.
\tag{4.15}
$$

Write
$$
\mathcal A:=R_P.
\tag{4.16}
$$
We reserve the letter $A$ from the problem for the base ring, which will be $\Bbbk$. Since $\mathcal O$ is $\pi$-adically separated and (4.15) is injective,
$$
\bigcap_{r\ge0}\pi^r\mathcal A=0.
\tag{4.17}
$$

Finally, localizing the isomorphism of Lemma 4.2 at $P$ gives
$$
\mathcal A/\pi\mathcal A\simeq E_N=B.
\tag{4.18}
$$
Indeed, the complement of $P$ maps exactly to $E\setminus N$.

## 5. The height of $P$

This is the only substantial dimension estimate. Put
$$
K_0=\Bbbk(\pi),\qquad
\mathcal B=K_0[x_0,y_0,z_0].
\tag{5.1}
$$
We have
$$
R[1/\pi]=T=\Bbbk[\pi,\pi^{-1},x_0,y_0,z_0]\subseteq\mathcal B.
$$
After localizing $R$ at $P$ and then inverting $\pi$, every nonzero $f\in\Bbbk[\pi]$ becomes a unit: write $f=\pi^r u$ with $u(0)\ne0$; then $u\in R\setminus P$, while $\pi$ is inverted at the second stage. Hence
$$
\mathcal A[1/\pi]=(R\setminus P)^{-1}\mathcal B.
\tag{5.2}
$$

For a prime $Q\subset\mathcal B$, put, using the generic identifications $S_n\subseteq\mathcal B$,
$$
I_n=Q\cap S_n.
$$
Call $Q$ **persistent** if
$$
I_n\subseteq\mathfrak m_n\qquad\text{for every }n.
\tag{5.3}
$$
By (5.2) and (4.13), persistence is exactly the condition that $Q$ survive in $\mathcal A[1/\pi]$: it is equivalent to $Q\cap(R\setminus P)=\varnothing$.

### Lemma 5.1

Let $Q\subset\mathcal B$ be persistent, let $q=Q\cap R$, and set
$$
L=\operatorname{Frac}(\mathcal B/Q).
$$
There exists a valuation ring of $L$ dominating $\mathcal A/q$. More explicitly, the local rings
$$
T_n=(S_n/I_n)_{\mathfrak m_n/I_n}
$$
form a nested local system and
$$
\bigcup_{n\ge0}T_n=\mathcal A/q.
\tag{5.4}
$$
Thus a valuation ring of $L$ dominating their union exists.

### Proof

Since the generic maps are inclusions and $I_{n+1}\cap S_n=I_n$, each
$$
T_n\to T_{n+1}
$$
is injective. Equations (4.6) send all generators of $\mathfrak m_n$ into $\mathfrak m_{n+1}$, while an element with nonzero constant term retains nonzero constant term. Thus $\mathfrak m_{n+1}\cap S_n=\mathfrak m_n$, and the maps are local.

Every numerator of $\mathcal A/q$ and every denominator from $R\setminus P$ occurs at a finite stage, whence (5.4). The ring $\bigcup T_n$ is local with maximal ideal induced by $P$. Its fraction field is $L$: localizing a finite stage $S_n/I_n$ at $\Bbbk[\pi]\setminus\{0\}$ gives $\mathcal B/Q$, because $Q$ is its contraction. Localization does not change the fraction field. The domination theorem now supplies the required valuation ring of $L$. $\square$

Assume from now on that $Q$ is persistent and
$$
\operatorname{ht}_{\mathcal B}Q=2.
\tag{5.5}
$$
Let $\nu$ be the valuation of $L=\operatorname{Frac}(\mathcal B/Q)$ furnished by Lemma 5.1. It is trivial on $\Bbbk^\times$, because those elements are units in every $T_n$. Since $\pi\in P\setminus q$,
$$
\delta:=\nu(\pi)>0.
$$
For every $n$, $x_{n+1}\in P$, while $\gamma_n\in\Bbbk^\times$, so $x_{n+1}+\gamma_n\notin P$; it is a unit of $\mathcal A$. From (4.6),
$$
z_n=\pi(x_{n+1}+\gamma_n),
$$
and therefore
$$
\nu(z_n)=\delta\quad\text{for every }n.
\tag{5.6}
$$

Because $\mathcal B$ is a three-dimensional polynomial ring over $K_0$, condition (5.5) gives
$$
\operatorname{trdeg}_{K_0}L=1,\qquad
\operatorname{trdeg}_{\Bbbk}L=2.
$$
By the Zariski–Abhyankar inequality,
$$
\operatorname{ratrank}\Gamma_\nu+\operatorname{trdeg}_{\Bbbk}\kappa(\nu)\le2.
\tag{5.7}
$$
Since $\nu(\pi)>0$, $\nu$ is nontrivial. Its rank is therefore one or two.

We keep the fixed compatible scalar orbit
$$
q_n=(\xi_n,\eta_n,\zeta_n)\in\mathfrak m^3
$$
from (4.3)–(4.5). It satisfies exactly the same equations (4.6) after evaluation in $\mathcal O$.

### Lemma 5.2 (uniform contraction)

Let $F_1\supseteq K_0$ carry a rank-one valuation $w$ whose restriction to $K_0$ is the $\pi$-adic valuation, normalized by $w(\pi)=1$. Suppose $F_1$ contains elements at every level satisfying (4.6), all of nonnegative $w$-value and with every nonzero coordinate of positive value; call this a compatible centered state. Suppose also that some $\varepsilon>0$ is a lower bound for the $w$-value of every nonzero coordinate of every state. Then the level-zero state of $F_1$ equals $q_0=(\xi_0,\eta_0,\zeta_0)$ in the $w$-adic completion $\widehat F_1$. Consequently such a state in $L=\operatorname{Frac}(\mathcal B/Q)$ cannot lie on the nonzero prime $Q$ of $\mathcal B$.

### Proof

Embed the rank-one group $\Gamma_w$ into $\mathbf R$. The inclusion $K_0\hookrightarrow F_1$ preserves the $\pi$-adic valuation, so completions give an injection
$$
\Bbbk((\pi))=\widehat K_0\hookrightarrow\widehat F_1.
\tag{5.8}
$$
Thus $q_n$ and the $F_1$-state can be compared in $\widehat F_1$.

Let $\rho=\min\{\varepsilon,1\}$. At each level, every coordinate difference has value at least $\rho$: the $F_1$-coordinate is either zero or has value at least $\varepsilon$, and every scalar coordinate lies in $\pi\Bbbk[[\pi]]$. Let $d\ge\rho$ be the minimum of the three next-level differences, after passing to the incoming target frame. The matrices $M_n\in\operatorname{GL}_2(\Bbbk)$ preserve this minimum.

Subtract the two copies of (4.6). Digits cancel. In characteristic two,
$$
X^2-X'^2=(X-X')^2,\qquad Y^2-Y'^2=(Y-Y')^2,
$$
and
$$
XY-X'Y'=X(Y-Y')+Y'(X-X').
$$
The old $z$-difference has value at least $1+d$. The old $v$-difference has value at least
$$
\min\{2d,1+d\}.
$$
The old $u$-difference has value at least
$$
\begin{cases}
\min\{d+\rho,1+d\},&F_n=XY,\\
\min\{2d,1+d\},&F_n=Y^2.
\end{cases}
$$
Since $d\ge\rho$ and $1\ge\rho$, each bound is at least $d+\rho$. Iterating from level $N$ back to level $0$ yields
$$
d_0\ge d_N+N\rho\ge(N+1)\rho.
$$
The level-zero difference is fixed, while $N$ is arbitrary. Hausdorffness forces it to be zero.

If the $F_1$-state lies on a nonzero prime $Q$, then every $f\in Q$ vanishes there. Equality with $q_0$ in $\widehat F_1$, together with the injection (5.8), makes $f(\xi_0,\eta_0,\zeta_0)=0$. This contradicts algebraic independence of $q_0$ over $K_0$. $\square$

### Lemma 5.3

Under (5.5), the valuation $\nu$ cannot have rank one.

### Proof

Suppose it does and normalize $\delta=\nu(\pi)=1$. By (5.6), all nonzero $z_n$ have value $1$. If all nonzero plane coordinates had a common positive lower bound, Lemma 5.2 would already give a contradiction. Choose therefore a nonzero plane coordinate $u_1$ at some stage with
$$
0<c:=\nu(u_1)<\frac14.
\tag{5.9}
$$
Let $e\in M$ be its nonzero special class. For every $a\in K_\partial^\times$, $ae\in M$. Choose lifts $u_a\in\mathcal A$ with $u_a\bmod\pi=ae$, taking $u_0=0$, $u_1$ as above, and $u_\lambda=\lambda u_1$ for $\lambda\in\Bbbk$. For nonzero $a,b$, reduction modulo $\pi\mathcal A$ gives
$$
\begin{aligned}
u_au_{a^{-1}}-u_1^2&\in\pi\mathcal A,\\
u_au_b-u_{ab}u_1&\in\pi\mathcal A,\\
u_a+u_b-u_{a+b}&\in\pi\mathcal A.
\end{aligned}
\tag{5.10}
$$
Each error has $\nu$-value at least $1$.

If $u_a$ vanished in $L$ for some $a\ne0$, the first relation would give $u_1^2=$ an element of value at least $1$, contradicting $2c<1$. Thus, setting $d(a)=\nu(u_a)$, the two terms in the first line of (5.10) must have the same value:
$$
d(a)+d(a^{-1})=2c,\qquad 0<d(a)<2c.
\tag{5.11}
$$
In the second line, both possible values are less than $1$, because $c<1/4$. Hence
$$
d(a)+d(b)=d(ab)+c.
$$
Thus
$$
\lambda(a):=d(a)-c
$$
is a group homomorphism $K_\partial^\times\to\Gamma_\nu$. For every integer $m$,
$$
0<d(a^m)=c+m\lambda(a).
$$
Embed the rank-one group in $\mathbf R$; taking $m\to\pm\infty$ forces $\lambda(a)=0$. Therefore
$$
d(a)=c\qquad(a\in K_\partial^\times).
\tag{5.12}
$$

Define
$$
\rho:K_\partial\longrightarrow\kappa(\nu),\qquad
\rho(a)=\operatorname{res}_\nu(u_a/u_1),\quad \rho(0)=0.
$$
After division of the third line of (5.10) by $u_1$, its error has positive value $1-c$. After division of the second by $u_1^2$, its error has positive value $1-2c$. Thus $\rho$ is additive and multiplicative. It fixes $\Bbbk$, by the chosen lifts, and (5.12) shows that every nonzero $u_a/u_1$ is a residue unit. Hence $\rho$ is an injective field homomorphism.

Put
$$
v=\frac{u_t}{u_1}\in L.
$$
It has value $0$, and its residue $\rho(t)$ is transcendental over $\Bbbk$. It follows that $v$ is transcendental over $K_0$: scale a hypothetical relation to have coefficients in the $\pi$-adic valuation ring with minimum value $0$, and reduce; the reduction would be a nonzero polynomial relation for $\rho(t)$ over $\Bbbk$. Since $\operatorname{trdeg}_{K_0}L=1$,
$$
L/K_0(v)
$$
is finite.

The restriction of $\nu$ to $K_0(v)$ is the Gauss extension of the $\pi$-adic valuation: in a nonzero polynomial in $v$, terms whose coefficients have minimum $\pi$-order cannot cancel after reduction because $\overline v=\rho(t)$ is transcendental. Its value group is therefore $\mathbf Z$. The finite-extension inequality gives
$$
[\Gamma_\nu:\mathbf Z]<\infty.
\tag{5.13}
$$
A finite-index ordered overgroup of $\mathbf Z$ is discrete. Its positive elements consequently have a common positive lower bound, contradicting Lemma 5.2. $\square$

### Lemma 5.4

Under (5.5), the valuation $\nu$ cannot have rank two.

### Proof

Suppose $\Gamma_\nu$ has rank two. It has a unique nonzero proper convex subgroup $\Delta$. Let $\nu_1$ be the rank-one coarsening with value group $\Gamma_\nu/\Delta$. Recall $\delta=\nu(\pi)>0$.

**Case 1: $\delta\notin\Delta$.** Then $\nu_1(\pi)>0$. Coarse reduction gives a homomorphism
$$
B=\mathcal A/\pi\mathcal A\longrightarrow\kappa(\nu_1).
\tag{5.14}
$$
Its kernel $J$ is prime. Every element of $B\setminus M$ lifts to a unit of the local ring $\mathcal A$, hence maps to a nonzero residue; thus $J\subseteq M$.

Suppose some nonzero plane state coordinate has $\nu$-value in $\Delta$. Its $\nu_1$-value is then $0$, so its coarse residue is nonzero. Its special class is a nonzero element of $M$, and hence $J\ne M$. Since $\operatorname{Spec}B=\{(0),M\}$, this forces $J=0$. Then (5.14) embeds $\operatorname{Frac}B$ into $\kappa(\nu_1)$. By Lemma 2.1,
$$
\operatorname{trdeg}_{\Bbbk}\operatorname{Frac}B=2.
$$
But $\nu_1$ is a nontrivial valuation of $L/\Bbbk$, and $\operatorname{trdeg}_{\Bbbk}L=2$; Abhyankar gives
$$
\operatorname{trdeg}_{\Bbbk}\kappa(\nu_1)\le1,
$$
a contradiction.

Therefore no nonzero plane state coordinate has value in $\Delta$. Every nonzero memory coordinate has positive $\nu_1$-value by (5.6), and so does $\pi$. At each finite stage, a nonzero element in the maximal ideal is a finite sum of the images of
$$
\pi,\ x_n,\ y_n,\ z_n,
$$
with coefficients in the valuation ring. Hence it has positive $\nu_1$-value. An element outside that maximal ideal has original value $0$, hence $\nu_1$-value $0$. Thus $\nu_1$ dominates every finite-stage local transform and hence $\mathcal A/q$. It is rank one and extends the $\pi$-adic valuation. Lemma 5.3 gives a contradiction.

**Case 2: $\delta\in\Delta$.** Then $\nu_1$ is trivial on $K_0$ but nontrivial on $L$. Choose $s\in L^\times$ with $\nu_1(s)>0$. The element $s$ must be transcendental over $K_0$: an extension of a trivial valuation to a finite extension is trivial, since the value-group quotient is torsion and an ordered abelian group is torsion-free. As $\operatorname{trdeg}_{K_0}L=1$,
$$
L/K_0(s)
$$
is finite. The restriction of $\nu_1$ to $K_0(s)$ is the $s$-adic valuation, whose residue field is $K_0$. The finite-extension inequality gives
$$
F:=\kappa(\nu_1)\ \text{is finite over }K_0.
\tag{5.15}
$$
The original rank-two valuation is the composite of $\nu_1$ with a rank-one valuation $\nu_2$ on $F$, with value group $\Delta$. Since $\delta\in\Delta$, $\nu_2$ extends the $\pi$-adic valuation. Normalize $\nu_2(\pi)=1$.

Every state coordinate has nonnegative $\nu_1$-value. If that value is positive, its coarse residue is $0$. If it is zero and the coordinate is nonzero, its original value lies in $\Delta_{>0}$, so its coarse residue has positive $\nu_2$-value. Digits and elements of $K_0$ have coarse value zero. Thus the coarse residues form a compatible centered $F$-valued state satisfying (4.6). For every $f\in Q$, this state satisfies $f=0$ in $F$. Likewise, a denominator inverted in a finite-stage localization has original value zero, so its coarse residue is nonzero and has $\nu_2$-value zero.

By (5.15) and the finite-extension inequality again, $\nu_2$ is discrete and finitely ramified over the $\pi$-adic valuation. Hence its positive values have a common positive lower bound. Lemma 5.2, applied over $F_1=F$, makes the level-zero coarse residue state equal to
$$
(\xi_0,\eta_0,\zeta_0)
$$
in $\widehat F_{\nu_2}$. But the completion map
$$
\Bbbk((\pi))\hookrightarrow\widehat F_{\nu_2}
$$
is injective. Since the coarse state lies on $V(Q)$ and $Q\ne0$, this contradicts algebraic independence of $q_0$ over $K_0$. $\square$

### Proposition 5.5

The local ring $\mathcal A=R_P$ has dimension two.

### Proof

Lemmas 5.3 and 5.4 show that no persistent prime $Q\subset\mathcal B$ has height two. If a persistent prime had height at least three, it would contain a height-two prime, because $\mathcal B=K_0[x_0,y_0,z_0]$ is Noetherian and catenary; a subprime of a persistent prime is persistent. Hence every persistent prime has height at most one. By the prime correspondence in (5.2),
$$
\dim\mathcal A[1/\pi]\le1.
\tag{5.16}
$$

Next $\operatorname{ht}_{\mathcal A}(\pi\mathcal A)=1$. Indeed, (4.18) shows $\pi\mathcal A$ is prime. If
$$
0\ne\mathfrak q\subsetneq(\pi)
$$
and $0\ne a\in\mathfrak q$, write $a=\pi a_1$. Since $\pi\notin\mathfrak q$ and $\mathfrak q$ is prime, $a_1\in\mathfrak q$. Iterating gives
$$
a\in\bigcap_{r\ge0}\pi^r\mathcal A,
$$
contradicting (4.17).

Now let
$$
\mathfrak q_0\subsetneq\cdots\subsetneq\mathfrak q_\ell=P
$$
be a strict chain. Suppose first that some $\mathfrak q_i$ with $i<\ell$ contains $\pi$. Since $\mathfrak q_i\ne P$, and the primes of $\mathcal A$ containing $(\pi)$ correspond to the two primes $(0),M$ of $B=\mathcal A/\pi\mathcal A$, necessarily $\mathfrak q_i=(\pi)$. There is no nonzero prime below $(\pi)$, and no prime strictly between $(\pi)$ and $P$. Hence the chain is contained in
$$
(0)\subsetneq(\pi)\subsetneq P,
$$
so $\ell\le2$.

Otherwise $\mathfrak q_0,\ldots,\mathfrak q_{\ell-1}$ all avoid $\pi$. Localizing them at $\pi$ preserves strict inclusions. Indeed, if $a\in\mathfrak q_{i+1}\setminus\mathfrak q_i$ but $a/1\in\mathfrak q_i[1/\pi]$, then $\pi^ma\in\mathfrak q_i$ for some $m$; since $\pi\notin\mathfrak q_i$, primality gives $a\in\mathfrak q_i$, a contradiction. Thus (5.16) gives $\ell-1\le1$, so again $\ell\le2$. Since
$$
(0)\subsetneq(\pi)\subsetneq P
$$
is strict, $\dim\mathcal A=\operatorname{ht}P=2$. $\square$

## 6. Failure of Jaffardness at $P$

By (4.18), reduction modulo $\pi$ gives
$$
\mathcal A[X]/(\pi)\simeq B[X].
$$
Take the chain from Lemma 2.2:
$$
(0)\subsetneq Q_B\subsetneq M[X]\subsetneq(M,X)
\quad\text{in }B[X].
$$
Its inverse images in $\mathcal A[X]$ are distinct primes containing $\pi\mathcal A[X]$. Prepending the zero ideal, which lies strictly below $(\pi)$ in the domain $\mathcal A[X]$, gives a chain of four strict inclusions:
$$
(0)\subsetneq(\pi)
   \subsetneq\widetilde{Q_B}
   \subsetneq\widetilde{M[X]}
   \subsetneq\widetilde{(M,X)}.
$$
Hence
$$
\dim\mathcal A[X]\ge4.
\tag{6.1}
$$
By Proposition 5.5,
$$
\dim\mathcal A=2.
\tag{6.2}
$$
Thus $\mathcal A$ is finite-dimensional, but
$$
\dim\mathcal A[X]\ge4\ne3=\dim\mathcal A+1.
$$
Therefore $\mathcal A=R_P$ is not Jaffard.

## 7. The required embeddings and finiteness assumptions

Finally take, in the notation of the problem,
$$
\boxed{
A=\Bbbk,\qquad
D=R,\qquad
T=\Bbbk[\pi,\pi^{-1},x_0,y_0,z_0],\qquad
P=\{r\in R:r\bmod\pi R\in N\}.
}
\tag{7.1}
$$

These satisfy all required conditions:

* $A=\Bbbk$ is a field, hence a Noetherian domain with $1\ne0$.
* $T$ is a Laurent polynomial ring over $\Bbbk$. Equivalently,
  $$
  T\cong
  \Bbbk[\Pi,U,X_0,Y_0,Z_0]/(\Pi U-1),
  $$
  so it is finitely generated as a $\Bbbk$-algebra and is an integral domain.
* The inclusions are the literal ones constructed in (4.8)–(4.9):
  $$
  \Bbbk\subseteq S_0\subseteq R=\bigcup_{n\ge0}S_n\subseteq T.
  $$
  All maps preserve $1$. We did not assume that $D$ is finitely generated over $A$.
* $P$ is prime by (4.12), and under the identification $\mathcal A=D_P$,
  $$
  \dim D_P=2,\qquad\dim D_P[X]\ge4.
  $$

Consequently $D_P$ fails the defining one-variable equality for a Jaffard domain, while all embeddings and stated finiteness assumptions in the assertion are retained. This disproves the assertion. $\blacksquare$

## References

1. Viet-Hoang Tran, Thieu N. Vo and Tan M. Nguyen, *Bouvier’s conjecture is true*, arXiv:2609.01887v1, 2026, §§3–5 (the boundary domain, the lift and the height argument). [Version 1](https://arxiv.org/html/2609.01887v1).
2. The Stacks Project Authors, *The Stacks Project*, Lemma 10.50.2, domination by a valuation ring. [Tag 00I8](https://stacks.math.columbia.edu/tag/00I8).
3. Franz-Viktor Kuhlmann, *Valuation Theory*, online book manuscript, Chapter 6, §6.4, Lemma 6.31, p. 152. This is the valued-field form of the transcendence-degree inequality, without a characteristic or valuation-rank restriction. [Chapter 6](https://www.fvkuhlmann.de/bookch6.pdf).
4. Franz-Viktor Kuhlmann, *Valuation Theory*, online book manuscript, Chapter 7, Theorem 7.49, the fundamental inequality for finite extensions. [Chapter 7](https://www.fvkuhlmann.de/bookch7.pdf).
5. Irena Swanson and Craig Huneke, *Integral Closure of Ideals, Rings, and Modules*, London Mathematical Society Lecture Note Series 336, Cambridge University Press, 2006, Propositions 6.6.4 and 6.6.6, pp. 131–132 (convex subgroups, coarsenings and rank). [Author-hosted PDF](https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf).
