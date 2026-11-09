# Solution

For $u=(u_1,u_2,u_3)\in \mathbb N^3$ write $x^u=x^{u_1}y^{u_2}z^{u_3}$, and define

$$
\omega(u)=\frac{u_1}{a}+\frac{u_2}{b}+\frac{u_3}{c}.
$$

For $n\ge 1$ set

$$
E_n=\{u\in\mathbb N^3:\omega(u)\ge n\},
\qquad
J_n=(x^u:u\in E_n)\subseteq k[x,y,z].
$$

The following finite arithmetic condition is the criterion.

$$
\boxed{
\begin{array}{l}
\text{For every }(i,j,k)\in\mathbb N^3\text{ with }i<a,\ j<b,\ k<c\text{ and }\omega(i,j,k)\ge2,\\[2mm]
\text{there is }(p,q,r)\in\mathbb N^3\text{ with }0\le p\le i,\ 0\le q\le j,\ 0\le r\le k\\[1mm]
\text{such that }\omega(p,q,r)\ge1\text{ and }\omega(i-p,j-q,k-r)\ge1.
\end{array}}
\tag{$\ast$}
$$

Equivalently, with $L=\operatorname{lcm}(a,b,c)$, $A=L/a$, $B=L/b$, $C=L/c$, the test is:

- loop over $0\le i<a$, $0\le j<b$, $0\le k<c$;
- if $Ai+Bj+Ck<2L$, ignore $(i,j,k)$;
- otherwise search $0\le p\le i$, $0\le q\le j$, $0\le r\le k$ for
  $$
  Ap+Bq+Cr\ge L
  \quad\text{and}\quad
  A(i-p)+B(j-q)+C(k-r)\ge L.
  $$
  If one such $(p,q,r)$ is not found, output “not normal”; otherwise continue.

The loops are finite for every fixed triple: there are at most
$$
\sum_{i<a}\sum_{j<b}\sum_{k<c}(i+1)(j+1)(k+1)
=
\frac{a(a+1)b(b+1)c(c+1)}8
$$
inner checks. Thus this is an algorithmic criterion that terminates for every triple.

The theorem is:

> **Theorem.** For every positive triple $(a,b,c)$, the ideal $I_{a,b,c}$ is normal if and only if condition $(\ast)$ holds. In particular, whether $(a,b,c)$ qualifies is independent of the field $k$.

We prove this.

---

## 1. A monomial integral-closure lemma

We first recall that $\overline H$ is an ideal for every ideal $H$. Indeed, let $A=R[Ht]\subseteq R[t]$ be the Rees algebra. Then $u\in\overline H$ iff $ut$ is integral over $A$: one direction follows by multiplying an equation of integral dependence by $t^m$; the converse follows by taking the coefficient of $t^m$ in a monic equation for $ut$. Integral elements over a subring form a subring, so $\overline H$ is closed under sums and multiplication by elements of $R$. This argument is valid over every field.

Define a weight valuation

$$
\nu(f)=\min\{\omega(u):\text{the coefficient of }x^u\text{ in }f\text{ is nonzero}\},
\qquad \nu(0)=+\infty.
$$

Because $k[x,y,z]$ is a domain and $\omega$ is linear, $\nu(fg)=\nu(f)+\nu(g)$ for nonzero $f,g$.

We shall use the following lemma.

**Lemma.** Let $H$ be a monomial ideal and let $n\ge1$. Assume

1. every monomial in $H$ has weight at least $n$;
2. $x^{na},y^{nb},z^{nc}\in H$.

Then $\overline H=J_n$.

**Proof.** First prove $J_n\subseteq\overline H$. Take $u\in E_n$, and put $W=\omega(u)\ge n$. Since $W>0$, define

$$
\lambda_1=\frac{u_1/a}{W},\qquad
\lambda_2=\frac{u_2/b}{W},\qquad
\lambda_3=\frac{u_3/c}{W}.
$$

Then $\lambda_i\ge0$ and $\lambda_1+\lambda_2+\lambda_3=1$. Also

$$
\lambda_1(na,0,0)+\lambda_2(0,nb,0)+\lambda_3(0,0,nc)
=
\frac nW\,u.
$$

Since $W\ge n$, the vector $\rho=(1-n/W)u$ has nonnegative rational coordinates. Choose $N>0$ clearing denominators so that $N\lambda_i\in\mathbb N$ and $N\rho\in\mathbb N^3$. Then

$$
Nu
=
(N\lambda_1)(na,0,0)
+(N\lambda_2)(0,nb,0)
+(N\lambda_3)(0,0,nc)
+N\rho.
$$

Because $x^{na},y^{nb},z^{nc}\in H$, and because
$$
N\lambda_1+N\lambda_2+N\lambda_3=N,
$$
we get $x^{Nu}\in H^N$. Hence $x^u$ is integral over $H$: take the equation
$$
T^N-x^{Nu}=0
$$
with coefficient $-x^{Nu}\in H^N$. Thus every monomial generator of $J_n$ lies in $\overline H$; since $\overline H$ is an ideal, $J_n\subseteq\overline H$.

Now let $f\in\overline H$. Suppose some monomial of $f$ is outside $E_n$. Then $t:=\nu(f)<n$. Let
$$
f^m+c_1f^{m-1}+\cdots+c_m=0,\qquad c_i\in H^i,
$$
be an equation of integral dependence. Every monomial in $H^i$ is a product of $i$ monomials of $H$, each of weight at least $n$, so $\nu(c_i)\ge ni$. Therefore, for $i\ge1$,
$$
\nu(c_i f^{m-i})
\ge ni+(m-i)t
=mt+i(n-t)
>mt.
$$
But $\nu(f^m)=mt$. The right-hand side $-c_1f^{m-1}-\cdots-c_m$ has valuation $>mt$, so it cannot equal $f^m$, whose valuation is $mt$. This contradiction shows that every monomial of $f$ lies in $E_n$, i.e. $f\in J_n$. Hence $\overline H\subseteq J_n$, and the lemma follows. $\square$

---

## 2. Computing $I_{a,b,c}$ and the closures of its powers

Apply the lemma with $H=(x^a,y^b,z^c)$ and $n=1$. Its hypotheses are immediate, and $J_1$ is exactly the monomial ideal with exponent set $E_1$. Hence

$$
I_{a,b,c}=\overline{(x^a,y^b,z^c)}=J_1.
\tag{1}
$$

Now fix $n\ge1$. Since $I=J_1$, every monomial in $I^n$ is a product of $n$ monomials from $E_1$, and therefore has weight at least $n$. Also $x^a,y^b,z^c\in I$, so
$$
x^{na},y^{nb},z^{nc}\in I^n.
$$
Thus the lemma applies to $H=I^n$, giving

$$
\overline{I^n}=J_n
\quad\text{for every }n\ge1.
\tag{2}
$$

We also need the exponent set of $I^n$. For a monomial $x^u$,

$$
x^u\in I^n
\iff
u\in nE_1,
\tag{3}
$$

where $nE_1=E_1+\cdots+E_1$ is the $n$-fold Minkowski sum. Indeed, one direction is immediate from the definition of $I^n$. Conversely, if $x^u\in I^n$, then $u\ge v_1+\cdots+v_n$ for some $v_i\in E_1$. Put $\gamma=u-\sum v_i\in\mathbb N^3$. Since $E_1+\mathbb N^3\subseteq E_1$, replacing $v_n$ by $v_n+\gamma$ gives an expression $u\in nE_1$.

Combining (2) and (3), normality is equivalent to

$$
E_n=nE_1\qquad\text{for every }n\ge1.
\tag{4}
$$

The inclusion $nE_1\subseteq E_n$ always holds, so what matters is $E_n\subseteq nE_1$.

---

## 3. Reduction to the square

Let $P(n)$ denote the assertion $E_n\subseteq nE_1$. We already know $P(1)$, indeed $E_1=E_1$.

Assume $P(2)$. We prove $P(n)$ for all $n\ge3$ by induction. Suppose $P(m)$ holds for all $m<n$, and take $u=(u_1,u_2,u_3)\in E_n$.

If $u_1\ge a$, then
$$
u-(a,0,0)\in E_{n-1},
$$
because its weight is $\omega(u)-1\ge n-1$. By $P(n-1)$, $u-(a,0,0)\in(n-1)E_1$. Since $(a,0,0)\in E_1$, it follows that $u\in nE_1$. The same argument applies if $u_2\ge b$ or $u_3\ge c$.

If no coordinate satisfies this, then $u_1<a$, $u_2<b$, $u_3<c$, and hence

$$
\omega(u)
\le
\frac{a-1}{a}+\frac{b-1}{b}+\frac{c-1}{c}
<3.
$$

But $u\in E_n$ and $n\ge3$, so $\omega(u)\ge n\ge3$, a contradiction. Thus $P(n)$ holds.

Consequently,

$$
I_{a,b,c}\text{ is normal}
\iff P(2).
\tag{5}
$$

More explicitly, $I$ is normal iff every element of $E_2$ is a sum of two elements of $E_1$.

---

## 4. The finite criterion

It remains to make $P(2)$ finite. Let $u=(i,j,k)\in E_2$.

If some coordinate is at least the corresponding pure exponent, say $i\ge a$, then
$$
u=(a,0,0)+\bigl(u-(a,0,0)\bigr),
$$
and $u-(a,0,0)\in E_1$. Thus $u\in2E_1$ automatically. Similarly for $j\ge b$ and $k\ge c$.

Therefore $P(2)$ is equivalent to checking only those $u\in E_2$ with

$$
0\le i<a,\qquad 0\le j<b,\qquad 0\le k<c.
$$

For such a $u$, membership $u\in2E_1$ means precisely that there is a decomposition
$$
u=v+(u-v),\qquad v\in E_1,\ u-v\in E_1.
$$
Writing $v=(p,q,r)$, this is exactly condition $(\ast)$. Hence $P(2)$ is equivalent to $(\ast)$. By the reduction in Section 3, $I_{a,b,c}$ is normal iff $(\ast)$ holds.

---

## 5. Correctness and termination of the algorithm

The algorithm displayed after the criterion is just condition $(\ast)$ with all rational inequalities multiplied by $L=\operatorname{lcm}(a,b,c)$. Therefore, by the theorem, it outputs “normal” exactly for the triples satisfying the criterion. Its loops are bounded by the displayed polynomial in $a,b,c$, so it terminates for every positive triple.

Finally, every step above used only exponent arithmetic and the fact that $k[x,y,z]$ is a domain. The proof that $\overline H$ is an ideal used the Rees algebra and is valid for arbitrary fields. No assumption on the characteristic or on algebraic closure was made. Hence the classification given by $(\ast)$ is the same over every field $k$.
