# Supplementary theorem. H-DRG for actual rooted trees

All graphs in this appendix are finite and simple.  For a graph \(G\), write

\[
I(G;x)=\sum_{k=0}^{\alpha(G)}i_k(G)x^k
\]

for its independence polynomial.  If \(B(x)=\sum_k b_kx^k\) has
nonnegative coefficients and \(B(z)>0\), its coefficient law at activity
\(z>0\) is the integer-valued law

\[
\Pr_{B,z}(X_B=k)=\frac{b_kz^k}{B(z)}.
\tag{A.1}
\]

Equivalently, for \(B=I(G;\cdot)\), the hard-core law on the independent
sets of \(G\) is

\[
\Pr_{G,z}(\mathcal I=I)=\frac{z^{|I|}}{I(G;z)}
\qquad (I\subseteq V(G)\text{ independent}),
\]

and \(X_B=|\mathcal I|\).  For a vertex \(r\), \(N[r]\) denotes its closed
neighborhood.  The notation \(U_n\asymp_Z W_n\) means that both ratios are
bounded above by positive constants depending only on \(Z\), for all
sufficiently large \(n\).

Its cumulants are

\[
K_m(B;z)=
\left.\frac{d^m}{dt^m}\log B(ze^t)\right|_{t=0}
\qquad (m\ge 1).
\tag{A.2}
\]

Thus \(K_1(B;z)=\mathbb E_{B,z}X_B\) and
\(K_2(B;z)=\operatorname{Var}_{B,z}X_B\).  We use

\[
\phi_{B,z}(\theta)=
\mathbb E_{B,z}\exp\{i\theta(X_B-K_1(B;z))\}
\tag{A.3}
\]

for the centered characteristic function.  An *actual forest law* means a
law of the form (A.1) with \(B=I(G;\cdot)\) for a finite forest \(G\).  A
product of actual forest laws at a common activity is again an actual forest
law, by taking disjoint union.  For polynomials \(B,D\), the notation
\(B\preceq D\) means coefficientwise domination.

Let \((T_i,r_i)_{i\in J}\) be a finite family of finite rooted trees; the
finite index set \(J\) may be empty.  Put

\[
P_i(x)=I(T_i;x),\qquad Q_i(x)=I(T_i-r_i;x),
\tag{A.4}
\]

\[
A(x)=\prod_{i\in J}P_i(x),\qquad
C(x)=\prod_{i\in J}Q_i(x),\qquad
F(x)=A(x)+xC(x)=\sum_jf_jx^j.
\tag{A.5}
\]

The two summands in \(F\) define a Bernoulli *root gate*: with probability

\[
q=\frac{A(z)}{F(z)}
\quad\text{the root is absent, and with probability}\quad
p=\frac{zC(z)}{F(z)}=1-q
\quad\text{the root is present.}
\tag{A.6}
\]

Conditional on absence, the remaining occupancy count has the \(A\)-law;
conditional on presence, it is one plus a random variable having the
\(C\)-law.

An integer \(s\) is an *interior integer saddle* for \(F\) at \(z\) if

\[
K_1(F;z)=s,\qquad 1\le s\le \deg F-1.
\tag{A.7}
\]

For such a saddle, let \(Y_A\) and \(Y_C\) have the \(A\)- and
\(C\)-coefficient laws at activity \(z\), respectively.  Set

\[
\mu_A=K_1(A;z),\qquad \mu_C=K_1(C;z),\qquad
V_A=K_2(A;z),\qquad V_C=K_2(C;z)
\tag{A.8}
\]

and

\[
\delta=1+\mu_C-\mu_A,
\qquad
v_i^P=K_2(P_i;z),\qquad v_i^Q=K_2(Q_i;z).
\tag{A.9}
\]

Conditioning on the gate gives

\[
V:=K_2(F;z)=qV_A+pV_C+pq\delta^2.
\tag{A.10}
\]

The diffuseness parameter of this decomposition is

\[
d=\frac1V\max\left(
\{pq\delta^2\}\cup
\{qv_i^P+pv_i^Q:i\in J\}
\right).
\tag{A.11}
\]

The maximum in (A.11) therefore includes the gate contribution even when
\(J=\varnothing\).

## A.1. Statement

### Theorem A.1 (H-DRG for actual rooted trees)

For every finite \(Z>0\), there exist constants

\[
\epsilon_D(Z)>0,\qquad V_D(Z)<\infty,
\]

such that the following holds.  For every finite family of finite rooted
trees, every \(0<z\le Z\), and every interior integer saddle \(s\) for the
polynomial \(F\) in (A.5),

\[
V\ge V_D(Z),\qquad d<\epsilon_D(Z)
\]

imply

\[
\boxed{f_s^2>f_{s-1}f_{s+1}}.
\tag{A.12}
\]

**Fourier input (Theorem D.1).**  For every \(0<L<\infty\), there are
constants \(c_L>0\) and \(\alpha_L\in(0,1)\) such that, for every finite
forest \(G\), every \(0<z\le L\), and every \(|\theta|\le\pi\),

\[
-\log|\phi_{I(G),z}(\theta)|
\ge c_L\min\{x,x^{\alpha_L}\},
\qquad
x=K_2(I(G);z)\theta^2,
\tag{A.13}
\]

where \(-\log 0=+\infty\).

Theorem D.1 is proved in Appendix D.

## A.2. Uniform moments and Fourier consequences

We first prove the moment estimate needed to turn (A.13) into local Gaussian
asymptotics.

### Lemma A.2 (uniform fourth moment for actual forests)

For every \(0<L<\infty\), there is \(C_L<\infty\) such that every finite
forest \(G\), every \(0<z\le L\), and the occupancy count \(X\) under its
hard-core law satisfy

\[
\mathbb E|X-\mathbb EX|^4
\le C_L\,\operatorname{Var}(X)\bigl(1+\operatorname{Var}(X)\bigr).
\tag{A.14}
\]

#### Proof

Root every component of \(G\), orient edges away from the roots, and let
\(T_v\) be the descendant subtree rooted at \(v\).  Let \(b_v\) be the
occupation probability of \(v\) in the free hard-core law on \(T_v\), and
put \(q_v=1-b_v\).  The tree recursion is

\[
\frac{b_v}{q_v}=z\prod_{u\text{ child of }v}q_u.
\tag{A.15}
\]

Consequently, with

\[
\eta=(1+L)^{-1},\qquad \rho=\frac{L}{1+L},
\]

one has \(q_v\ge\eta\) and \(b_v\le\rho\) at every vertex.

Let \(m_v^0,m_v^1\) be the conditional expected occupancy of \(T_v\) given
that \(v\) is absent or present, respectively, and write
\(\Delta_v=m_v^1-m_v^0\).  Conditioning on \(v\) gives the exact recursion

\[
\Delta_v=1-\sum_{u\text{ child of }v}b_u\Delta_u.
\tag{A.16}
\]

Take mutually independent Bernoulli variables \(B_v\) with means \(b_v\).
For a component root put \(R_v=1\), and for a nonroot put
\(R_v=1-X_{\operatorname{par}(v)}\); then define \(X_v=R_vB_v\).  Induction
from the leaves shows that \((X_v)_v\) has exactly the hard-core law.  Reveal
the \(B_v\)'s in an order in which parents precede children.  The Doob
martingale difference at \(v\) is

\[
D_v=R_v\Delta_v(B_v-b_v),
\qquad
X-\mathbb EX=\sum_vD_v.
\tag{A.17}
\]

Set

\[
a_v=b_vq_v\Delta_v^2,\qquad A_*=\sum_va_v,
\qquad w_v=\mathbb ER_v.
\]

For a nonroot vertex, the occupation probability of its parent is at most
\(b_{\operatorname{par}(v)}\le\rho\), so \(w_v\ge\eta\); for a root,
\(w_v=1\).  Orthogonality of martingale differences yields

\[
v:=\operatorname{Var}(X)=\sum_vw_va_v\ge\eta A_*.
\tag{A.18}
\]

The predictable quadratic variation is

\[
H=\sum_v\mathbb E(D_v^2\mid\mathcal F_{v^-})
=\sum_vR_va_v.
\]

Since \(0\le H\le A_*\) and \(\mathbb EH=v\),

\[
\mathbb EH^2\le A_*v\le\eta^{-1}v^2.
\tag{A.19}
\]

It remains to control the fourth powers of the increments.  Put

\[
s_v=\sum_{u\text{ child of }v}b_u,\qquad
t_v=\sum_{u\text{ child of }v}b_u\Delta_u^2,\qquad
\ell_v=\sum_{u\text{ child of }v}b_u\Delta_u.
\]

Equations (A.15) and \(q_u\le e^{-b_u}\) give
\(b_v\le Le^{-s_v}\), while

\[
t_v\le\eta^{-1}\sum_{u\text{ child of }v}a_u.
\tag{A.20}
\]

If \(|\Delta_v|\le2\), then
\(b_vq_v\Delta_v^4\le4a_v\).  If \(|\Delta_v|>2\), (A.16) implies
\(|\ell_v|>|\Delta_v|/2\), and weighted Cauchy--Schwarz gives
\(\ell_v^2\le s_vt_v\).  Therefore

\[
\begin{aligned}
b_vq_v\Delta_v^4
&\le16Le^{-s_v}s_v^2t_v^2\\
&\le64Le^{-2}\eta^{-2}
\left(\sum_{u\text{ child of }v}a_u\right)^2.
\end{aligned}
\tag{A.21}
\]

The child sets are disjoint as \(v\) varies.  Hence, for a constant depending
only on \(L\),

\[
\sum_v\mathbb ED_v^4
\le\sum_vb_vq_v\Delta_v^4
\le C_L(A_*+A_*^2)
\le C_L(v+v^2).
\tag{A.22}
\]

The finite-martingale fourth-moment estimate (D.18), proved in Lemma D.3,
applies to the real martingale differences in (A.17).  Together with
(A.19) and (A.22), it gives

\[
\mathbb E\left|\sum_vD_v\right|^4
\le \left(\frac{128}{9}\right)^2\mathbb EH^2
   +6\sum_v\mathbb ED_v^4
\le C_Lv(1+v).
\]

This is (A.14).  \(\square\)

The next lemma records both the near-center local expansion and the
rank-uniform estimates that will be used later.

### Lemma A.3 (diffuse local expansion and rank-uniform smoothing)

Fix \(0<L<\infty\).  For each \(n\), let

\[
B_n(x)=\prod_i I(G_{n,i};x)
\]

be a finite product of independence polynomials of finite forests, all
evaluated at a common activity \(0<z_n\le L\).  Let \(X_{n,i}\) be the factor
occupancy counts and set

\[
S_n=\sum_iX_{n,i},\qquad
\mu_n=\mathbb ES_n,\qquad
W_n=\operatorname{Var}(S_n),\qquad
M_n=\max_i\operatorname{Var}(X_{n,i}).
\tag{A.23}
\]

Assume

\[
W_n\longrightarrow\infty,
\qquad
\frac{M_n}{W_n}\longrightarrow0.
\tag{A.24}
\]

If \(k_n\in\mathbb Z\) and

\[
x_n=\frac{k_n-\mu_n}{\sqrt{W_n}}\longrightarrow x\in\mathbb R,
\tag{A.25}
\]

write \(\beta_{n,r}=\Pr(S_n=k_n+r)\) for \(r=-1,0,1\).  With
\(\varphi(x)=(2\pi)^{-1/2}e^{-x^2/2}\), one has

\[
\sqrt{W_n}\,\beta_{n,0}\longrightarrow\varphi(x),
\tag{A.26}
\]

\[
W_n(\beta_{n,1}-\beta_{n,0})\longrightarrow\varphi'(x),
\qquad
W_n(\beta_{n,-1}-\beta_{n,0})\longrightarrow-\varphi'(x),
\tag{A.27}
\]

\[
W_n^{3/2}(\beta_{n,-1}+\beta_{n,1}-2\beta_{n,0})
\longrightarrow\varphi''(x),
\tag{A.28}
\]

and

\[
W_n^2(\beta_{n,0}^2-\beta_{n,-1}\beta_{n,1})
\longrightarrow\varphi(x)^2.
\tag{A.29}
\]

In particular, if \(x_n\to0\), then, with

\[
u_n=\frac{\beta_{n,-1}}{\beta_{n,0}},\qquad
v_n=\frac{\beta_{n,1}}{\beta_{n,0}},\qquad
\kappa_n=1-u_nv_n,
\qquad
\vartheta_n=\frac12\log\frac{u_n}{v_n},
\tag{A.30}
\]

one has

\[
\beta_{n,0}=\frac{1+o(1)}{\sqrt{2\pi W_n}},\qquad
\kappa_n=\frac{1+o(1)}{W_n},\qquad
\vartheta_n=o(W_n^{-1/2}).
\tag{A.31}
\]

Independently of (A.24), if \(G\) is any finite forest with variance \(W>0\)
at \(0<z\le L\), then uniformly over all integers \(k\),

\[
\Pr(X_G=k)=O_L(W^{-1/2}),
\tag{A.32}
\]

\[
\Pr(X_G=k\pm1)-\Pr(X_G=k)=O_L(W^{-1}),
\tag{A.33}
\]

\[
\Pr(X_G=k-1)+\Pr(X_G=k+1)-2\Pr(X_G=k)
=O_L(W^{-3/2}).
\tag{A.34}
\]

#### Proof

Let \(v_{n,i}=\operatorname{Var}(X_{n,i})\).  Lemma A.2 gives

\[
\frac1{W_n^2}\sum_i
\mathbb E|X_{n,i}-\mathbb EX_{n,i}|^4
\le C_L\left(\frac1{W_n}+\frac{M_n}{W_n}\right)\longrightarrow0.
\tag{A.35}
\]

The Lyapunov central limit theorem therefore yields

\[
\frac{S_n-\mu_n}{\sqrt{W_n}}\Rightarrow N(0,1).
\tag{A.36}
\]

Put

\[
\Phi_n(u)=
\mathbb E\exp\left\{iu\frac{S_n-\mu_n}{\sqrt{W_n}}\right\}.
\]

The disjoint union of the \(G_{n,i}\) is a finite forest.  Theorem D.1,
applied to that whole forest, gives for \(|u|\le\pi\sqrt{W_n}\)

\[
|\Phi_n(u)|
\le\exp\{-c_L\min(u^2,|u|^{2\alpha_L})\}.
\tag{A.37}
\]

Extend \(\Phi_n\) by zero outside this interval.  The right side of (A.37),
multiplied by \(1+|u|+u^2\), is integrable on \(\mathbb R\).  By (A.36),
\(\Phi_n(u)\to e^{-u^2/2}\) pointwise.

Fourier inversion gives

\[
\beta_{n,r}=\frac1{2\pi\sqrt{W_n}}
\int_{\mathbb R}\Phi_n(u)e^{-ix_nu}e^{-iru/\sqrt{W_n}}\,du.
\tag{A.38}
\]

Dominated convergence applied directly to (A.38) proves (A.26).  For the
first differences, use

\[
\sqrt{W_n}\bigl(e^{\mp iu/\sqrt{W_n}}-1\bigr)
\longrightarrow\mp iu,
\qquad
\sqrt{W_n}\left|e^{\mp iu/\sqrt{W_n}}-1\right|\le|u|.
\tag{A.39}
\]

This gives (A.27).  For the centered second difference, use

\[
W_n\bigl(e^{iu/\sqrt{W_n}}+e^{-iu/\sqrt{W_n}}-2\bigr)
\longrightarrow-u^2
\tag{A.40}
\]

and the corresponding bound by \(u^2\), proving (A.28).

Let \(a_{n,\pm}=\beta_{n,\pm1}-\beta_{n,0}\).  The exact identity

\[
\beta_{n,0}^2-\beta_{n,-1}\beta_{n,1}
=-\beta_{n,0}(a_{n,-}+a_{n,+})-a_{n,-}a_{n,+}
\tag{A.41}
\]

together with (A.26)--(A.28) gives

\[
\begin{aligned}
W_n^2(\beta_{n,0}^2-\beta_{n,-1}\beta_{n,1})
&\longrightarrow
-\varphi(x)\varphi''(x)+\varphi'(x)^2\\
&=\varphi(x)^2,
\end{aligned}
\]

which is (A.29).  Dividing (A.29) by (A.26) squared proves the assertion for
\(\kappa_n\).  The dominated-convergence argument is uniform when \(x_n\)
ranges over a fixed compact interval, so (A.26)--(A.27) also give

\[
\vartheta_n
=-\frac{\varphi'(x_n)}{\varphi(x_n)\sqrt{W_n}}
+o(W_n^{-1/2})
=\frac{x_n}{\sqrt{W_n}}+o(W_n^{-1/2}),
\]

which proves (A.31) when \(x_n\to0\).

Finally, for a single forest, Theorem D.1 and the substitution
\(u=\sqrt W\,\theta\) give, for \(m=0,1,2\),

\[
\begin{aligned}
\int_{-\pi}^{\pi}|\theta|^m|\phi_{I(G),z}(\theta)|\,d\theta
&\le W^{-(m+1)/2}
\int_{\mathbb R}|u|^m
e^{-c_L\min(u^2,|u|^{2\alpha_L})}\,du\\
&=O_L(W^{-(m+1)/2}).
\end{aligned}
\tag{A.42}
\]

In Fourier inversion the rank-dependent phase has modulus one.  The
multipliers for a first difference and a centered second difference are
bounded respectively by \(|\theta|\) and \(\theta^2\).  Equations
(A.32)--(A.34) follow from (A.42).  \(\square\)

## A.3. Actual deletion and the gate dichotomy

### Lemma A.4 (root-deletion variance and odds bounds)

For the rooted-tree composition (A.4)--(A.10), at every \(0<z\le Z\),

\[
\frac pq=z\frac{C(z)}{A(z)}\le z\le Z,
\qquad q\ge\frac1{1+Z},
\tag{A.43}
\]

\[
V_C\le(1+Z)V_A,
\tag{A.44}
\]

and

\[
V_A\le(1+3Z)V_C+2\log\frac{zq}{p}.
\tag{A.45}
\]

If in addition \(d\le1/2\), then

\[
V_A\ge\frac{V}{2(1+Z)}.
\tag{A.46}
\]

For every fixed \(Z\), there is \(V_*(Z)<\infty\) such that, whenever
\(V\ge V_*(Z)\) and \(d\le1/2\), at least one of the following alternatives
holds:

\[
p\le V^{-3},
\tag{A.47}
\]

or

\[
V_C\ge\frac{V}{4(1+Z)(1+3Z)}.
\tag{A.48}
\]

In the second alternative,

\[
V_A\asymp_ZV_C\asymp_ZV.
\tag{A.49}
\]

#### Proof

For one rooted tree \((T,r)\), put

\[
P=I(T;x),\qquad Q=I(T-r;x),\qquad
R=I(T-N[r];x).
\]

Then

\[
P=Q+xR,
\qquad R\preceq Q\preceq P.
\tag{A.50}
\]

At activity \(z\), let

\[
b=\frac{zR(z)}{P(z)},\qquad g=\frac{R(z)}{Q(z)}.
\tag{A.51}
\]

Under the \(P\)-law, \(b\) is the probability that the root is occupied.
Conditional on root absence the count has the \(Q\)-law, and conditional on
root presence it is one plus a variable having the \(R\)-law.  The law of
total variance therefore gives

\[
v_P=(1-b)v_Q+bv_R
+b(1-b)(1+\mu_R-\mu_Q)^2.
\tag{A.52}
\]

In particular, \(v_P\ge(1-b)v_Q\).  Since

\[
\frac{b}{1-b}=z\frac{R(z)}{Q(z)}\le z\le Z,
\]

we obtain

\[
v_Q\le(1+Z)v_P.
\tag{A.53}
\]

Under the \(Q\)-law, the event that every neighbor of \(r\) is absent has
probability \(g\), and the conditional law on that event is the \(R\)-law.
Another application of total variance gives

\[
v_Q\ge gv_R,
\qquad
(\mu_R-\mu_Q)^2\le\frac{1-g}{g}v_Q.
\tag{A.54}
\]

Moreover \(b/g=z(1-b)\le Z\).  Substituting (A.54) into (A.52), and using
\((1+u)^2\le2+2u^2\), gives

\[
\begin{aligned}
v_P
&\le v_Q+\frac bgv_Q+2b
   +2b(1-b)\frac{1-g}{g}v_Q\\
&\le(1+3Z)v_Q+2b.
\end{aligned}
\tag{A.55}
\]

Summing (A.53) over \(i\) proves (A.44).  If \(b_i\) denotes the root
occupation probability in the \(P_i\)-law, then

\[
\frac{C(z)}{A(z)}=\prod_i(1-b_i),
\qquad
\sum_i b_i\le\sum_i-\log(1-b_i)=\log\frac{A(z)}{C(z)}.
\tag{A.56}
\]

Since \(A(z)/C(z)=zq/p\), summing (A.55) proves (A.45).

Coefficientwise inclusion \(C\preceq A\) gives (A.43).  If \(d\le1/2\),
then \(pq\delta^2\le V/2\).  Equations (A.10) and (A.44) consequently give

\[
\frac V2\le qV_A+pV_C
\le\{q+p(1+Z)\}V_A\le(1+Z)V_A,
\]

which proves (A.46).

Suppose now that \(p>V^{-3}\).  By (A.43) and (A.56),

\[
0\le\log\frac{zq}{p}\le\log(ZV^3).
\tag{A.57}
\]

For all sufficiently large \(V\), depending only on \(Z\), the final term
in (A.45) is at most \(V/[4(1+Z)]\).  Combining (A.45) and (A.46) yields
(A.48).  Finally, \(V\ge qV_A\), (A.43), and (A.44) give the required upper
bounds in (A.49), while (A.46) and (A.48) give the lower bounds.  \(\square\)

## A.4. The balanced gate

The following lemma proves the two-channel comparison needed when neither
gate state is rare.

### Lemma A.5 (balanced two-channel determinant)

Fix \(0<Z<\infty\) and \(\eta,\lambda>0\).  Consider any sequence of
rooted-tree compositions (A.4)--(A.10), at activities \(0<z_n\le Z\), with
integer parent saddles \(s_n\), and write
\(F_n(x)=\sum_j f_{n,j}x^j\).  Assume that

\[
V_n\to\infty,\qquad p_n,q_n\ge\eta,\qquad
V_{A,n},V_{C,n}\ge\lambda V_n,
\tag{A.58}
\]

\[
\frac1{V_n}\max_i(q_nv_{i,n}^P+p_nv_{i,n}^Q)\to0,
\qquad
\frac{p_nq_n\delta_n^2}{V_n}\to0.
\tag{A.59}
\]

Then

\[
f_{n,s_n}^2>f_{n,s_n-1}f_{n,s_n+1}
\]

for all sufficiently large \(n\).

#### Proof

Equation (A.10) and \(p_n,q_n\ge\eta\) imply

\[
\lambda V_n\le V_{A,n},V_{C,n}\le\eta^{-1}V_n.
\tag{A.60}
\]

Moreover,

\[
\frac{\max_i v_{i,n}^P}{V_{A,n}},
\frac{\max_i v_{i,n}^Q}{V_{C,n}}
\le\frac1{\eta\lambda V_n}
\max_i(q_nv_{i,n}^P+p_nv_{i,n}^Q)\longrightarrow0.
\tag{A.61}
\]

The parent saddle identity is

\[
s_n=\mu_{A,n}+p_n\delta_n.
\]

Hence the displacements of the \(A\)-target \(s_n\) and the \(C\)-target
\(s_n-1\) from their respective means are

\[
h_{A,n}=p_n\delta_n,
\qquad
h_{C,n}=-q_n\delta_n.
\tag{A.62}
\]

By (A.58)--(A.60), both are \(o(\sqrt{V_{A,n}})\) and
\(o(\sqrt{V_{C,n}})\), respectively.

For \(r=-1,0,1\), define

\[
\alpha_r=\Pr_{A_n,z_n}(Y_A=s_n+r),
\qquad
\chi_r=\Pr_{C_n,z_n}(Y_C=s_n-1+r).
\tag{A.63}
\]

Lemma A.3 applies separately to the two channel products.  Put

\[
u_A=\frac{\alpha_{-1}}{\alpha_0},\quad
v_A=\frac{\alpha_1}{\alpha_0},\quad
\kappa_A=1-u_Av_A,\quad
\vartheta_A=\frac12\log\frac{u_A}{v_A},
\]

and define \(u_C,v_C,\kappa_C,\vartheta_C\) analogously.  Equations
(A.31) and (A.60) give

\[
\begin{aligned}
\alpha_0&=\frac{1+o(1)}{\sqrt{2\pi V_A}},&
\kappa_A&=\frac1{V_A}+o(V_n^{-1}),&
\vartheta_A&=o(V_n^{-1/2}),\\
\chi_0&=\frac{1+o(1)}{\sqrt{2\pi V_C}},&
\kappa_C&=\frac1{V_C}+o(V_n^{-1}),&
\vartheta_C&=o(V_n^{-1/2}).
\end{aligned}
\tag{A.64}
\]

The two pure channel determinants are positive eventually.  For the mixed
term, the identities

\[
u_B=\sqrt{1-\kappa_B}\,e^{\vartheta_B},
\qquad
v_B=\sqrt{1-\kappa_B}\,e^{-\vartheta_B}
\qquad (B=A,C)
\]

give

\[
\begin{aligned}
\frac{2\alpha_0\chi_0-\alpha_{-1}\chi_1
-\alpha_1\chi_{-1}}{\alpha_0\chi_0}
&=2-u_Av_C-v_Au_C\\
&=2\left[1-\sqrt{(1-\kappa_A)(1-\kappa_C)}
\cosh(\vartheta_A-\vartheta_C)\right]\\
&=\frac1{V_A}+\frac1{V_C}+o(V_n^{-1}).
\end{aligned}
\tag{A.65}
\]

The last quantity is positive eventually because (A.60) gives
\(V_A^{-1}+V_C^{-1}\ge2\eta/V_n\).

Let \(\pi_r\) be the parent probability at rank \(s_n+r\).  Exact gate
conditioning gives

\[
\pi_r=q_n\alpha_r+p_n\chi_r.
\tag{A.66}
\]

Expanding its determinant,

\[
\begin{aligned}
\pi_0^2-\pi_{-1}\pi_1
={}&q_n^2(\alpha_0^2-\alpha_{-1}\alpha_1)
+p_n^2(\chi_0^2-\chi_{-1}\chi_1)\\
&+p_nq_n(2\alpha_0\chi_0-
\alpha_{-1}\chi_1-\alpha_1\chi_{-1}).
\end{aligned}
\tag{A.67}
\]

Every term on the right is positive for all sufficiently large \(n\).
Finally,

\[
\pi_r=\frac{f_{n,s_n+r}z_n^{s_n+r}}{F_n(z_n)},
\]

so the positive prefactor cancels from the three-point determinant and the
claimed coefficient inequality follows.  \(\square\)

## A.5. Proof of Theorem A.1

#### Proof

Fix \(Z>0\).  Suppose, contrary to the theorem, that no pair of constants
\(\epsilon_D(Z)>0\) and \(V_D(Z)<\infty\) has the asserted property.  For
each \(n\ge1\), choose a rooted-tree composition, an activity
\(0<z_n\le Z\), and an interior integer saddle \(s_n\) such that

\[
V_n\ge n,
\qquad
d_n<\frac1n,
\qquad
f_{n,s_n}^2\le f_{n,s_n-1}f_{n,s_n+1}.
\tag{A.68}
\]

After passage to a subsequence, either \(p_n\to0\) or
\(\liminf_n p_n>0\).

Suppose first that \(\liminf_n p_n>0\).  Equation (A.43) bounds \(q_n\) away
from zero.  Since \(d_n\to0\), Lemma A.4 gives
\(V_{A,n}\ge V_n/[2(1+Z)]\).  Furthermore,

\[
0\le\log\frac{z_nq_n}{p_n}=O_Z(1),
\]

so (A.45) gives \(V_{C,n}\ge c_ZV_n\) for all sufficiently large \(n\).
The two channel variances are also \(O_Z(V_n)\), by (A.10), (A.43), and
(A.44).  Finally, (A.11) gives both limits in (A.59).  Lemma A.5 applies and
contradicts (A.68).  We may therefore assume

\[
p_n\longrightarrow0,
\qquad q_n\longrightarrow1.
\tag{A.69}
\]

For all sufficiently large \(n\), (A.46) and \(V_n\ge q_nV_{A,n}\) give

\[
V_{A,n}\asymp_ZV_n.
\tag{A.70}
\]

Also,

\[
\frac{\max_i v_{i,n}^P}{V_{A,n}}
\le\frac{d_nV_n}{q_nV_{A,n}}\longrightarrow0.
\tag{A.71}
\]

The \(A\)-channel displacement from the parent saddle is exactly

\[
h_{A,n}=s_n-\mu_{A,n}=p_n\delta_n.
\tag{A.72}
\]

Using (A.11), (A.43), and (A.70),

\[
\frac{h_{A,n}^2}{V_{A,n}}
=\frac{p_n}{q_n}\frac{p_nq_n\delta_n^2}{V_{A,n}}
\le C_Zp_nd_n\longrightarrow0.
\tag{A.73}
\]

Lemma A.3, applied to the \(A\)-product at target \(s_n\), now gives, with

\[
\alpha_r=\Pr_{A_n,z_n}(Y_A=s_n+r),
\qquad r=-1,0,1,
\]

\[
D_A:=\alpha_0^2-\alpha_{-1}\alpha_1\ge c_ZV_n^{-2},
\tag{A.74}
\]

\[
\alpha_0=O_Z(V_n^{-1/2}),\qquad
\alpha_{\pm1}-\alpha_0=O_Z(V_n^{-1}),
\tag{A.75}
\]

\[
\alpha_{-1}+\alpha_1-2\alpha_0=O_Z(V_n^{-3/2}).
\tag{A.76}
\]

Lemma A.4 divides every sufficiently large index into the alternatives
(A.47) and (A.48).  We show that (A.68) is impossible in either alternative.

If \(p_n\le V_n^{-3}\), define

\[
\chi_r=\Pr_{C_n,z_n}(Y_C=s_n-1+r),
\qquad r=-1,0,1.
\]

Only \(0\le\chi_r\le1\) is needed.  From (A.66)--(A.67),

\[
\left|(\pi_0^2-\pi_{-1}\pi_1)-q_n^2D_A\right|
=O_Z(p_nV_n^{-1/2}+p_n^2)=o(V_n^{-2}).
\tag{A.77}
\]

Equations (A.69), (A.74), and (A.77) imply
\(\pi_0^2-\pi_{-1}\pi_1>0\), contrary to (A.68).

It remains to treat indices for which \(p_n>V_n^{-3}\).  Equations
(A.44), (A.46), and (A.48) give

\[
V_{A,n}\asymp_ZV_{C,n}\asymp_ZV_n.
\tag{A.78}
\]

The polynomial \(C_n\) is the independence polynomial of the actual forest
\(\bigsqcup_i(T_{n,i}-r_{n,i})\).  Apply the rank-uniform part of Lemma A.3
to this whole forest, at the original activity \(z_n\le Z\) and the arbitrary
rank \(s_n-1\).  It gives

\[
\chi_0=O_Z(V_n^{-1/2}),\qquad
\chi_{\pm1}-\chi_0=O_Z(V_n^{-1}),
\tag{A.79}
\]

\[
\chi_{-1}+\chi_1-2\chi_0=O_Z(V_n^{-3/2}).
\tag{A.80}
\]

Set

\[
a_\pm=\alpha_{\pm1}-\alpha_0,
\qquad
c_\pm=\chi_{\pm1}-\chi_0.
\]

The mixed and pure \(C\)-determinants satisfy the exact identities

\[
\begin{aligned}
X_{AC}
&:=2\alpha_0\chi_0-
\alpha_{-1}\chi_1-\alpha_1\chi_{-1}\\
&=-\alpha_0(c_-+c_+)-\chi_0(a_-+a_+)
-a_-c_+-a_+c_-,
\end{aligned}
\tag{A.81}
\]

\[
D_C:=\chi_0^2-\chi_{-1}\chi_1
=-\chi_0(c_-+c_+)-c_-c_+.
\tag{A.82}
\]

Equations (A.75)--(A.76) and (A.79)--(A.80) therefore imply

\[
|X_{AC}|+|D_C|=O_Z(V_n^{-2}).
\tag{A.83}
\]

Using the exact determinant expansion (A.67), (A.69), (A.74), and (A.83),
we obtain

\[
\begin{aligned}
\pi_0^2-\pi_{-1}\pi_1
&=q_n^2D_A+p_nq_nX_{AC}+p_n^2D_C\\
&\ge V_n^{-2}\{q_n^2c_Z-O_Z(p_n)-O_Z(p_n^2)\}>0
\end{aligned}
\tag{A.84}
\]

for all sufficiently large \(n\), again contradicting (A.68).

Thus no sequence (A.68) exists.  By the exact negation used to construct
that sequence, there must be constants \(\epsilon_D(Z)>0\) and
\(V_D(Z)<\infty\) for which (A.12) holds.  Since \(Z>0\) was arbitrary, the
theorem follows.  \(\square\)
