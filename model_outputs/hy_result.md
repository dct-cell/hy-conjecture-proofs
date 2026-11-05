## Counterexample

The answer to Problem 32(b) is **negative**. We construct a one-dimensional Noetherian local domain $D$ in which every nonzero divisorial ideal is $2$-$v$-generated, but whose maximal ideal is divisorial and not stable.

The construction works over any field $k$; take $k=\mathbb Q$ for definiteness. Put
$$
V=k[[t]],\qquad K=k((t)),
$$
and let
$$
D=k[[t^4,t^5,t^{11}]]\subset V.
$$

For fractional ideals $I,J$, write
$$
(I:J)=\{x\in K:xJ\subseteq I\},\qquad
I^{-1}=(D:I),\qquad I^v=(D:I^{-1}).
$$

The value semigroup of $D$ is
$$
H=\{0,4,5\}\cup\{n\in\mathbb N:n\ge 8\}
   =\langle 4,5,11\rangle.
$$
Thus, as a $k$-vector space,
$$
D=k\oplus kt^4\oplus kt^5\oplus t^8V. \tag{1}
$$

### 1. Basic properties of $D$

The ring $D$ is the image of the complete Noetherian local ring
$k[[X,Y,Z]]$ under $X\mapsto t^4$, $Y\mapsto t^5$, $Z\mapsto t^{11}$. Hence $D$ is a Noetherian local domain.

Moreover,
$$
V=D+tD+t^2D+t^3D,
$$
so $V$ is a finite $D$-module. Since $t=t^5/t^4\in \operatorname{Frac}(D)$, the two domains have quotient field $K$, and $V=k[[t]]$ is the integral closure of $D$. Therefore
$$
\dim D=\dim V=1.
$$
In particular, $D$ is a one-dimensional Noetherian domain, hence a Mori domain.

The maximal ideal of $D$ is
$$
M=kt^4\oplus kt^5\oplus t^8V=(t^4,t^5,t^{11})D. \tag{2}
$$
The conductor is
$$
C=(D:V)=t^8V. \tag{3}
$$

---

## 2. Classification of the divisorial ideals

We prove first that every nonzero divisorial fractional ideal of $D$ is $2$-$v$-generated.

Set
$$
A=D/C,\qquad \mathcal E=V/D.
$$
By (1), $A$ has $k$-basis $1,x,y$, where
$$
x=\overline{t^4},\qquad y=\overline{t^5}.
$$
Its maximal ideal is
$$
\mathfrak m=kx\oplus ky,\qquad \mathfrak m^2=0.
$$

Also, $\mathcal E$ has basis
$$
e_1=\bar t,\quad e_2=\overline{t^2},\quad e_3=\overline{t^3},
\quad e_6=\overline{t^6},\quad e_7=\overline{t^7}.
$$
The $A$-module structure is given by
$$
\begin{array}{c|ccccc}
 &e_1&e_2&e_3&e_6&e_7\\ \hline
x&0&e_6&e_7&0&0\\
y&e_6&e_7&0&0&0 .
\end{array} \tag{4}
$$
Put
$$
S=ke_6\oplus ke_7.
$$
From (4),
$$
\mathfrak m\mathcal E=S,\qquad
\operatorname{Ann}_{\mathcal E}(\mathfrak m)=S. \tag{5}
$$

### The annihilator closure

Here $L(U)$, also written $D+U$, denotes the inverse image in $V$ of an $A$-submodule $U\subseteq V/D$; when computing $(1,u)^v$, formula (6) is applied to $A\bar u$.

For a subspace $U\subseteq\mathcal E$, let $L(U)\subseteq V$ be the $D$-module with
$$
L(U)/D=U.
$$
Define
$$
U^\perp=\operatorname{Ann}_A(U),\qquad
U^{\perp\perp}=\{z\in\mathcal E:U^\perp z=0\}.
$$

Because $1\in L(U)$ and $C=(D:V)$,
$$
(D:L(U))=C+\widetilde{U^\perp},
$$
where $\widetilde{U^\perp}$ is any lift of $U^\perp$ to $D$. Taking the colon once more gives
$$
L(U)^v=L(U^{\perp\perp}). \tag{6}
$$

If $U\neq 0$, then $U^\perp\subseteq\mathfrak m$: indeed, every element
$\lambda+r\in A$ with $\lambda\neq0$ and $r\in\mathfrak m$ is a unit, since
$\mathfrak m^2=0$.

Since $\dim_k\mathfrak m=2$, a nonzero closed $U=U^{\perp\perp}$ must therefore be one of the following.

* If $U^\perp=0$, then $U=\mathcal E$.
* If $U^\perp=\mathfrak m$, then by (5), $U=S$.
* If $U^\perp=kr$ for a nonzero
  $$
  r=\alpha x+\beta y,
  $$
  then $U=\ker(r:\mathcal E\to\mathcal E)$.

For
$$
z=a e_1+b e_2+c e_3+d e_6+f e_7,
$$
table (4) gives
$$
rz=(\alpha b+\beta a)e_6+(\alpha c+\beta b)e_7.
$$
Consequently,
$$
\ker r=S\oplus k p_r,
\qquad
p_r=\alpha^2e_1-\alpha\beta e_2+\beta^2e_3. \tag{7}
$$
Write
$$
K_r:=\ker r=S\oplus k p_r.
$$

Conversely,
$$
\operatorname{Ann}_A(S)=\mathfrak m,\qquad
\operatorname{Ann}_A(K_r)=kr,\qquad
\operatorname{Ann}_A(\mathcal E)=0.
$$
For the middle equality, observe that if $s=\gamma x+\delta y$, then
$$
s p_r
=
(\delta\alpha^2-\gamma\alpha\beta)e_6
+
(\gamma\beta^2-\delta\alpha\beta)e_7. \tag{8}
$$
The kernel of the map $(\gamma,\delta)\mapsto sp_r$ is exactly
$k(\alpha,\beta)$. Thus the map has one-dimensional kernel, while an element
of $A$ with nonzero scalar part cannot annihilate $p_r$.

Hence the complete list of closed subspaces of $\mathcal E$ is
$$
0,\qquad S,\qquad K_r\ \bigl(r\in\mathbb P(\mathfrak m)\bigr),\qquad
\mathcal E. \tag{9}
$$
By (6), these are exactly the normalized divisorial ideals between $D$ and $V$.

### Each one is $2$-$v$-generated

We now give explicit $v$-generators for each closed subspace in (9).

1. **The case $U=0$.**  
   Here $L(U)=D$, which is principal.

2. **The case $U=\mathcal E$.**  
   Take $u=t^2$. For $a=\lambda+\alpha x+\beta y\in A$,
   $$
   a\overline{t^2}
   =\lambda e_2+\alpha e_6+\beta e_7.
   $$
   Thus $\operatorname{Ann}_A(\overline{t^2})=0$, and (6) gives
   $$
   V=(1,t^2)^v. \tag{10}
   $$

3. **The case $U=S$.**  
   Take $u=t^6+t^7$. Since $\mathfrak m(e_6+e_7)=0$,
   $$
   \operatorname{Ann}_A(\overline{u})=\mathfrak m.
   $$
   Hence
   $$
   D+S=(1,t^6+t^7)^v. \tag{11}
   $$

4. **The case $U=K_r$.**  
   Let
   $$
   u_r=\alpha^2t-\alpha\beta t^2+\beta^2t^3,
   $$
   so that $\overline{u_r}=p_r$. By (8),
   $$
   \operatorname{Ann}_A(\overline{u_r})=kr.
   $$
   Therefore
   $$
   D+K_r=(1,u_r)^v. \tag{12}
   $$

Finally, let $I$ be any nonzero divisorial fractional ideal of $D$. Its set of $t$-adic values is bounded below; choose $a\in I$ of minimal value. Then
$$
L:=a^{-1}I
$$
satisfies
$$
D\subseteq L\subseteq V,\qquad 1\in L,
$$
and $L$ is still divisorial, because
$$
(qI)^v=qI^v\qquad(q\in K^\times).
$$
Thus $L=L(U)$ for one of the closed subspaces in (9). By (10)–(12),
$L=(1,u)^v$ except in the principal case, and hence
$$
I=aL=(a,au)^v.
$$
The case $L=D$ is principal.

Therefore:

> Every nonzero divisorial fractional ideal of $D$, and in particular every nonzero integral divisorial ideal of $D$, is $2$-$v$-generated.

---

## 3. The divisorial ideal that is not stable

We now show that the maximal ideal $M$ from (2) is a divisorial ideal which is not stable.

Put
$$
J=(t^4,t^5)D.
$$

### Step 1: $J^{-1}$

Let $q\in J^{-1}$ and put $a=qt^4$. Since $t^5=t\,t^4$,
$$
q\in J^{-1}
\iff a\in D\ \text{and}\ ta\in D.
$$
Writing an element of $D$ as in (1),
$$
a=a_0+a_4t^4+a_5t^5+r,\qquad r\in t^8V,
$$
the condition $ta\in D$ forces
$$
a_0=0,\qquad a_5=0.
$$
Consequently
$$
D\cap t^{-1}D=kt^4\oplus t^8V,
$$
and therefore
$$
J^{-1}=t^{-4}(kt^4+t^8V)=k+t^4V.
$$
Set
$$
B:=k+t^4V=D\oplus kt^6\oplus kt^7. \tag{13}
$$
Thus
$$
(D:J)=B. \tag{14}
$$

### Step 2: $(D:B)=M$

Because $1\in B$, any $q\in(D:B)$ lies in $D$. Moreover,
$$
qt^4V\subseteq D
\iff qt^4\in(D:V)=t^8V
\iff q\in t^4V.
$$
Hence
$$
(D:B)=D\cap t^4V=M.
$$
Together with (14), this gives
$$
J^v=M=(t^4,t^5,t^{11})D. \tag{15}
$$
Thus $M$ is $2$-$v$-generated and, since $v$ is idempotent, $M$ is divisorial.

Indeed,
$$
M^{-1}=B,\qquad M^v=(D:B)=M. \tag{16}
$$
For completeness, $J\subseteq M$ gives $M^{-1}\subseteq J^{-1}=B$, while
$$
BM=(k+t^4V)M\subseteq M+t^8V=M,
$$
so $B\subseteq M^{-1}$.

The $v$-operation genuinely adds the third generator: the value sets are
$$
v(J)=\{4,5,8,9,10\}\cup\{n:n\ge12\},
$$
whereas
$$
v(M)=\{4,5\}\cup\{n:n\ge8\}.
$$
In particular $t^{11}\in M\setminus J$.

### Step 3: the endomorphism ring of $M$

We claim
$$
E(M):=(M:M)=B. \tag{17}
$$

We have already seen that $BM=M$, so $B\subseteq(M:M)$. Conversely, if
$qM\subseteq M$, then
$$
qJ\subseteq qM\subseteq M\subseteq D,
$$
and hence $q\in(D:J)=B$. This proves (17).

### Step 4: $M$ is not invertible as an ideal of $E(M)$

We compute the inverse of $M$ as an ideal of $B$:
$$
(B:M)=\{q\in K:qM\subseteq B\}.
$$

Since $M\subseteq t^4V$,
$$
VM\subseteq t^4V\subseteq B,
$$
so $V\subseteq(B:M)$.

Conversely, suppose $0\neq q\in(B:M)$. Since $t^4,t^5\in M$,
$$
qt^4,\ qt^5\in B.
$$
The value semigroup of $B$ is
$$
v(B)=\{0\}\cup\{n:n\ge4\}.
$$
If $s=v(q)$, then both $s+4$ and $s+5$ must belong to $v(B)$. These are consecutive integers. The semigroup $\{0\}\cup[4,\infty)$ contains no such consecutive pair with $s<0$. Hence $s\ge0$, so $q\in V$. Therefore
$$
(B:M)=V. \tag{18}
$$

Finally,
$$
M(B:M)=MV.
$$
Because $M\subseteq t^4V$, we have $MV\subseteq t^4V$; since $t^4\in M$, also
$t^4V\subseteq MV$. Thus
$$
M(B:M)=MV=t^4V.
$$
But
$$
t^4V\subsetneq k+t^4V=B.
$$
Therefore
$$
M(B:M)\neq B.
$$
So $M$ is not invertible in its endomorphism ring $B=(M:M)$; equivalently, $M$ is not stable.

---

## Conclusion

The domain
$$
\boxed{D=k[[t^4,t^5,t^{11}]]}
$$
satisfies all the hypotheses of Problem 32(b):

1. $D$ is a one-dimensional Noetherian, hence Mori, domain.
2. Every nonzero divisorial ideal of $D$ is $2$-$v$-generated.
3. Its maximal ideal
   $$
   M=(t^4,t^5,t^{11})D=(t^4,t^5)^v
   $$
   is divisorial.
4. Nevertheless,
   $$
   (M:M)=k+t^4V,\qquad (k+t^4V:M)=V,
   $$
   and
   $$
   M(k+t^4V:M)=t^4V\ne k+t^4V.
   $$
   Hence $M$ is not stable.

Thus the implication proposed in Problem 32(b) is false.