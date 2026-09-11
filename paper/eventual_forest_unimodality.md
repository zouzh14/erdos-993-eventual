# Eventual unimodality of independence polynomials of finite forests

Ziheng Zou

[zouzh14@gmail.com](mailto:zouzh14@gmail.com)

Preprint, September 10, 2026

## Abstract

For a finite forest \(F\), let

\[
 I_F(x)=\sum_{k=0}^{\alpha(F)}i_k(F)x^k
\]

be its independence polynomial, where \(i_k(F)\) counts the independent
\(k\)-subsets of \(V(F)\) and \(\alpha(F)\) is the independence number. We
prove that there is an integer \(N_0\) such
that the coefficient sequence of \(I_F\) is unimodal whenever
\(|V(F)|\ge N_0\). Given a hypothetical counterexample, we consider the first
index at which its coefficient sequence rises after an earlier fall and tilt
the hard-core measure so that its mean is this index. We show that its activity
is less than 27 and that its variance diverges with the order. After rooting
the components, a martingale variance decomposition yields a vertex contributing
a fixed fraction of the total variance. At this vertex, the difference between
the conditional means under occupation and vacancy has a linear lower bound in
the forest order, while the conditional occupation probability stays bounded
away from zero. An exact alternating path expansion, on the other hand, shows
that this difference is sublinear in the order of the descendant subtree,
uniformly over all finite rooted trees at bounded activity. This contradiction
proves the theorem. The argument treats the forest at one common activity
rather than through componentwise products; any remaining counterexample must
lie below the resulting threshold.

**Keywords.** Independence polynomial, unimodality, finite forest, hard-core
model, martingale central limit theorem, local limit theorem.

## Introduction

The independence polynomial, introduced by Gutman and Harary [GH83], records
the number of independent vertex sets of each cardinality; see [LM05] for a
survey of its basic properties. Evaluated at a positive activity \(z\), it is
also the partition function of the hard-core lattice gas; the corresponding
probability law assigns weight proportional to \(z^{|S|}\) to each independent
set \(S\) [SS05]. This probabilistic interpretation is essential below, since
coefficient comparisons will be converted into local curvature statements for
the cardinality of a random hard-core independent set.

Independent-set sequences need not be unimodal for general graphs. Alavi,
Malde, Schwenk, and Erdős asked whether the independence polynomial of every
tree, or perhaps every forest, is unimodal [AMSE87]; this question is also
known as Erdős Problem 993. We establish the following asymptotic statement
for forests.

**Main Theorem.** There exists an integer \(N_0\) such that the coefficient
sequence of the independence polynomial of every finite forest with at least
\(N_0\) vertices is unimodal.

In particular, the same conclusion holds for every connected tree of order at
least \(N_0\). The proof treats a hypothetical nonunimodal forest as a whole,
at one first-recovery index and one common hard-core activity. Consequently,
every counterexample to Erdős Problem 993
has bounded order. This reduction is qualitative: the proof does not make the
order bound computationally explicit, and finitely many forest orders remain
untreated.

Several substantial subclasses were known before the present theorem.
Hamidoune proved log-concavity of the independent-set sequence for claw-free
graphs [Ham90], and Chudnovsky and Seymour later proved the stronger
real-rootedness of their independence polynomials [CS07]. For trees this
covers paths, since a tree is claw-free exactly when it has maximum degree at
most two. Levit and Mandrescu proved unimodality for several classes of
well-covered trees [LM03], while certain nonregular caterpillars satisfying
explicit pendant-multiplicity hypotheses, specified leaf-attachment families,
and other recursively described classes were treated in [BES18, GH18, ZC19].
More recently, Li, Li, Yang, and Zhang proved log-concavity for all spiders
[LLYZ25]. These results use family-specific coefficient arguments,
symmetric-function methods, or controlled branching geometry and do not give
a uniform argument for arbitrary trees.

There are also partial results that locate where a counterexample could
occur. Levit and Mandrescu proved that the last third of the independent-set
sequence of every bipartite graph, hence every tree, is decreasing [LM06].
The bipartite double count behind their result is also the starting point of
the activity localization in Proposition 2.2.
Basit and Galvin proved that a uniformly random labelled tree has long initial
increasing and terminal decreasing segments with probability tending to one
[BG21], and Heilman obtained a related exponentially high-probability initial
segment [Hei25]. These random-tree results leave an intermediate window and
do not apply uniformly to all trees. Exact computation established
log-concavity through order twenty [YMK21].

The tempting strengthening from unimodality to log-concavity is false.
Kadrawi and Levit found examples beginning at order twenty-six and constructed
two infinite non-log-concave tree families [KL23]. Galvin found failures much
farther into the coefficient sequence [Gal26], and Ramos and Sun used an
AI-guided search to produce a large experimental census of further examples
[RS25]. Linear-recurrence constructions now give families with several
consecutive log-concavity failures [BGG26]. Nevertheless, the original
Kadrawi--Levit families are unimodal [Li26], and symmetric unimodal tree
polynomials have also been constructed [HKV26]. These
developments show that log-concavity is not the missing invariant: substantial
local failures of log-concavity can coexist with unimodality.

The probabilistic language of the proof belongs to the hard-core-model
tradition. The occupancy-ratio recursion on a rooted tree and attenuation of
boundary influence are classical; see Weitz [Wei06] and the survey of Davies
and Kang [DK25]. The alternating path identity used in Section 5 is obtained
by logarithmically differentiating this recursion. The martingale central
limit theorem used in the variance argument is the constant-variance form of
Hall and Heyde [HH80]. Jain, Perkins, Sah, and Sawhney developed hard-core local
central limit estimates by Fourier inversion below the bounded-degree
uniqueness threshold [JPSS22]. Recent work studies bounds on the derivative of
the occupancy fraction with respect to the logarithm of the activity
[DST25, ZX26]. These bounded-degree results provide the closest analytic
precedents for the present argument. Here the degrees may be unbounded, the
activity is selected from the first recovery of the original forest, and the
local-limit analysis must determine the sign of a three-term log-concavity
determinant rather than only a point probability.

Our argument applies uniformly across all finite forest topologies and proceeds
directly through the hard-core measure rather than through real-rootedness or
log-concavity. Suppose that
\((F_n,s_n,z_n,V_n)\) is a sequence of canonical first-recovery states with
\(|V(F_n)|\to\infty\). Section 2 shows that \(0<z_n<27\) and
\(V_n\to\infty\). After rooting every component, the centered occupation count
has the martingale representation

\[
 X_n-\mathbb E X_n=\sum_{u\in F_n}\Delta_u\eta_u,
 \qquad V_n=\sum_{u\in F_n}a_up_uq_u\Delta_u^2.
\]

Theorem 4.1 gives a vertex \(u_n\) for which one summand in the variance identity
is at least \(\kappa_{27}V_n\). Theorems 4.2 and 4.3 then imply
\(p_{u_n}\ge\rho\) and \(|\Delta_{u_n}|\ge\delta|V(F_n)|\), for constants
\(\rho,\delta>0\). On the other hand, logarithmic differentiation of the
rooted-tree recursion gives

\[
 \Delta_{u_n}
 =\sum_{x\in T_{u_n}}(-1)^{d(u_n,x)}
   \prod_{y\in P(u_n,x)\setminus\{u_n\}}p_y,
\]

where \(P(u_n,x)\) is the unique path from \(u_n\) to \(x\). Since \(z_n<27\),
all factors in the product are uniformly bounded away from
one. The lower bound on \(p_{u_n}\) bounds the number of descendants for which the
path product exceeds any fixed threshold. Lemma 5.1 consequently gives
\(|\Delta_{u_n}|=o(|T_{u_n}|)\), uniformly over the relevant rooted trees. Since
\(|T_{u_n}|\le |V(F_n)|\), this contradicts the preceding linear lower bound.
The argument is qualitative: it gives no effective value of \(N_0\).

The analytic bridge used in the proof is stronger than weak convergence. If
integer-valued random variables have integer means \(s_n\) and variances
\(V_n\to\infty\), and if their normalized characteristic functions, extended
by zero outside their expanding lattice fundamental domains, converge in
quadratically weighted \(L^1(\mathbb R)\) to the characteristic function of a
twice continuously differentiable density \(f\), then Fourier
inversion gives

\[
 V_n^2\left[\Pr(X_n=s_n)^2-
 \Pr(X_n=s_n-1)\Pr(X_n=s_n+1)\right]
 \longrightarrow (f'(0))^2-f(0)f''(0).
\]

The exact two-variable inversion identity is proved in (B.16)--(B.21). This
weighted full-domain convergence, rather than a central limit theorem alone,
is what transfers a limiting density to adjacent coefficient curvature.

Appendices A and B establish the uniform Fourier and local-curvature estimates.
Appendices C and D develop the first-recovery bounds and the fixed variance
fraction theorem used in the main argument. Structurally, the proof rests on
the Doob variance decomposition for a parent-before-child reveal order and on
uniform attenuation in the rooted occupation recursion.

## 1. Independence polynomials and first recovery

All graphs in the paper are finite and simple. A forest need not be connected,
and an isolated vertex is allowed. Let \(F\) be a finite forest of order
\(N\), write \(i_k=i_k(F)\), and put \(\alpha=\alpha(F)\). We set
\(i_k=0\) outside \(0\le k\le\alpha\). A finite sequence is **unimodal** if
there is an index \(m\) such that it is nondecreasing through \(m\) and
nonincreasing thereafter. Equivalently, it never strictly rises after it has
strictly fallen. If the coefficient sequence of \(I_F\) is not unimodal,
define its **first-recovery index** by

\[
 s=s_*(F):=\min\{k\in\{0,\ldots,\alpha-1\}:\ i_k<i_{k+1}
       \text{ and }i_j>i_{j+1}\text{ for some }0\le j<k\}.
\]

Minimality gives

\[
 i_{s-1}\ge i_s<i_{s+1},
 \qquad i_s^2<i_{s-1}i_{s+1}.                       \tag{1.1}
\]

For \(z>0\), define the tilted hard-core law

\[
 \Pr_z(X=k)=\frac{i_kz^k}{I_F(z)},
\]

and write

\[
 K_1(I_F;z)=\mathbb E_zX=\frac{zI_F'(z)}{I_F(z)},
 \qquad K_2(I_F;z)=\operatorname{Var}_zX.
\]

Since

\[
 \frac{d}{d\log z}K_1(I_F;z)=K_2(I_F;z)>0,
\]

the function \(K_1(I_F;z)\) is strictly increasing. Its limits as \(z\downarrow0\)
and \(z\to\infty\) are \(0\) and \(\alpha(F)\), respectively, and (1.1) gives
\(1\le s\le\alpha(F)-1\). Hence there is a unique activity
\(z_s>0\) for which \(K_1(I_F;z_s)=s\).
The quadruple \((F,s,z_s,V)\), where \(V=K_2(I_F;z_s)\), is called the
**canonical first-recovery state** of \(F\). A **canonical first-recovery
sequence** is a sequence \((F_n,s_n,z_n,V_n)\) of such states, one for each
member of a sequence of nonunimodal finite forests. We call the sequence
**variance-divergent** if \(V_n\to\infty\).

At this activity, the second inequality in (1.1) is exactly the strict reverse log-concavity
inequality for the three central tilted probabilities:

\[
 \Pr_z(X=s)^2<\Pr_z(X=s-1)\Pr_z(X=s+1).             \tag{1.2}
\]

Throughout, first recovery refers only to the original forest at its common
activity; no component or boundary-conditioned descendant subtree is assigned
a recovery property.

## 2. Localization of a canonical counterexample

We first prove the quantitative reductions used at the end of the argument.

### Proposition 2.1 (index and variance-size localization)

For every nonunimodal \(N\)-vertex forest and its first-recovery state,

\[
 s>\frac{\sqrt N}{2},
 \qquad
 V\ge \frac{\sqrt N}{8(1+Z)^4}                     \tag{2.1}
\]

whenever \(z_s\le Z\).

**Proof.**
For the index bound, if \(1\le k\le\lfloor\sqrt N/2\rfloor\), every
nonindependent \(k\)-set contains an edge. Since a forest has at most \(N-1\)
edges, the union bound
gives

\[
 i_k\ge \binom Nk-(N-1)\binom{N-2}{k-2}
      =\binom Nk\left(1-\frac{k(k-1)}{N}\right)
      >\frac34\binom Nk,
\]

whereas, whenever this integer range is nonempty (and hence \(N\ge4\)),

\[
 i_{k-1}\le \binom N{k-1}
 =\binom Nk\frac{k}{N-k+1}\le \frac13\binom Nk.
\]

Thus \(i_{k-1}<i_k\) throughout that integer range. The first strict fall must
therefore occur at an index \(j\ge\lfloor\sqrt N/2\rfloor\), and its later
recovery satisfies \(s>j\). Since \(s\) is an integer, this proves
\(s>\sqrt N/2\).

For the variance bound, let \(H\) be the set of vertices of degree at least
three and let \(L\) be the set of vertices of degree one. Summing the identity
\(\sum_v(\deg v-2)=-2\) over the nontrivial components shows that

\[
 \sum_{v\in H}(\deg v-2)=|L|-2q,
\]

where \(q\) is the number of nontrivial components. Hence
\(|H|\le |L|\le N-|H|\), so \(|H|\le N/2\). At least \(N/2\) vertices
therefore have degree at most two. One color class of a bipartition of the
forest contains an independent set \(S\) of at least \(N/4\) such vertices.

Condition on the occupation variables outside \(S\). The variables in \(S\)
are then conditionally independent. A vertex in \(S\) has conditional variance
\(z/(1+z)^2\) when all its neighbors are absent, and zero otherwise. For any
vertex \(v\),

\[
 I_G(z)=I_{G-v}(z)+zI_{G-N[v]}(z)
       \le (1+z)I_{G-v}(z),
\]

so \(\Pr_z(v\notin I)\ge(1+z)^{-1}\). More explicitly, if
\(U=\{u_1,\ldots,u_m\}\) with \(m\le2\), apply the displayed inequality first
to \(G\), then to \(G-u_1\), and so on. This gives
\(I_G(z)\le(1+z)^mI_{G-U}(z)\), and hence
\(\Pr_z(U\cap I=\varnothing)\ge(1+z)^{-m}\). Apply this with
\(U=N(v)\), whose size is at most two. The conditional-variance identity now
gives

\[
 K_2(I_F;z)\ge \frac{Nz}{4(1+z)^4}.                 \tag{2.2}
\]

At the canonical activity, the elementary occupation bound
\(K_1(I_F;z)\le Nz/(1+z)\) and the index bound give
\(z>1/(2\sqrt N)\). Substituting this and \(z\le Z\) into (2.2) proves
(2.1). \(\square\)

### Proposition 2.2 (uniform activity localization)

Every first-recovery state of a finite forest satisfies

\[
 z_s<27.                                             \tag{2.3}
\]

**Proof.** Following the bipartite double-counting argument behind [LM06], let
\(\alpha\) be the independence number, and fix a bipartition with color classes
\(C_1,C_2\). For an independent \(k\)-set \(J\), let
\(A_r(J)\) be the vertices in \(C_r\setminus J\) that can be added to \(J\).
The set \(J\cup A_r(J)\) is independent, because \(C_r\) is independent and
every vertex of \(A_r(J)\) has no neighbor in \(J\). Consequently
\(|A_r(J)|\le\alpha-k\) for \(r=1,2\). Counting pairs \((J,v)\) for which
\(J\) is an independent \(k\)-set and \(J\cup\{v\}\) is independent gives

\[
 (k+1)i_{k+1}
 =\sum_{J:\,|J|=k}\bigl(|A_1(J)|+|A_2(J)|\bigr)
 \le2(\alpha-k)i_k.
\]

Thus a strict rise at \(k\) implies

\[
 k\le b:=\left\lfloor\frac{2\alpha-2}{3}\right\rfloor,
\]

so \(s\le b\). If \(\nu=N-\alpha\) is the matching number, König's theorem
[LP86] and the
three choices on each matching edge give

\[
 I_F(1)\le3^\nu2^{\alpha-\nu}\le3^\alpha.
\]

Put \(d=\alpha-b\). At \(z=27\),

\[
 I_F(27)(K_1(I_F;27)-b)
 =\sum_j(j-b)i_j27^j
 \ge27^b(d27^d-b3^\alpha)>0.
\]

For \(\alpha=3r,3r+1,3r+2\), the quotient \(d27^d/3^\alpha\) is respectively
\(27(r+1)\), \(9(r+1)\), and \(81(r+2)\), each larger than \(b\). Hence
\(K_1(I_F;27)>b\ge s\), and strict monotonicity of the tilted mean proves
(2.3). \(\square\)

Combining Propositions 2.1 and 2.2, any sequence of nonunimodal forests with
orders tending to infinity produces canonical states with

\[
 0<z_n<27,
 \qquad
 V_n\ge \frac{\sqrt{N_n}}{8\,28^4}\longrightarrow\infty. \tag{2.4}
\]

## 3. Rooted-tree recursion and the variance decomposition

Let \(I\) be the random independent set under the global hard-core law. Fix
one root in each component of \(F\), orient every edge away from its component
root, and let \(\mathcal R(F)\) be the set of component roots. Let \(T_x\)
denote the subtree induced by \(x\) and all of its descendants. Define

\[
 P_x(t)=I_{T_x}(t),
 \qquad Q_x(t)=I_{T_x-x}(t),
 \qquad A_x(t)=t\prod_{y\text{ child of }x}Q_y(t).
\]

Here \(P_x\) is the partition function with the parent of \(x\) absent,
\(Q_x\) is the partition function with \(x\) absent, and \(A_x\) is the
occupied contribution. The rooted-tree recursion is

\[
 Q_x(t)=\prod_{y\text{ child of }x}P_y(t),
 \qquad P_x(t)=Q_x(t)+A_x(t).
\]

Define the occupation odds, conditional occupation probability, and vacancy
probability by

\[
 R_x=\frac{A_x(z)}{Q_x(z)},
 \qquad p_x=\frac{R_x}{1+R_x},
 \qquad q_x=1-p_x.
\]

Equivalently, \(p_x=\Pr_z(x\in I\mid\operatorname{par}(x)\notin I)\), with the
virtual absent-parent convention at a component root, and
\(R_x=z\prod_{y\text{ child of }x}q_y\).

Define the **conditional mean difference** at \(x\) by

\[
 \Delta_x=\mathbb E_z(|I\cap T_x|\mid x\in I)
              -\mathbb E_z(|I\cap T_x|\mid x\notin I).
\]

If \(a_x\) denotes the probability that the parent of \(x\) is absent in the
global hard-core law, with a virtual absent parent and \(a_r=1\) for every
\(r\in\mathcal R(F)\), define the **vertex variance contribution** at \(x\) by

\[
 g(x)=a_xp_xq_x\Delta_x^2.                           \tag{3.1}
\]

Write \(\xi_x=\mathbf 1_{\{x\in I\}}\), with
\(\xi_{\operatorname{par}(r)}=0\) for a component root, and set

\[
 \eta_x=\xi_x-p_x(1-\xi_{\operatorname{par}(x)}).
\]

Since \(p_x\) is this conditional occupation probability, the variables
\(\eta_x\) are martingale differences in a parent-before-child ordering, with
\(\mathbb E\eta_x^2=a_xp_xq_x\). The recursion
\(\Delta_x+\sum_{y\text{ child of }x}p_y\Delta_y=1\) makes the coefficient of
each \(\xi_x\) in \(\sum_x\Delta_x\eta_x\) equal to one. Thus
\(\sum_x\Delta_x\eta_x=X-\sum_xp_x\Delta_x\); taking expectations gives
\(\mathbb EX=\sum_xp_x\Delta_x\), and hence

\[
 X-\mathbb EX=\sum_{x\in F}\Delta_x\eta_x.
\]

Thus each vertex contributes the orthogonal variance \(g(x)\), and

\[
 V=\sum_{x\in F}g(x).                                \tag{3.2}
\]

The boundary-conditioned hard-core laws on \(T_x\), taken with this fixed
rooting, determine \(p_x,q_x,\Delta_x\), while \(a_x\) records the position of
\(T_x\) in its rooted component.

## 4. A vertex carrying a fixed variance fraction and the scale of first recovery

### Theorem 4.1 (a vertex carrying a fixed variance fraction)

There are constants \(\kappa_{27}>0\) and \(V_{27}<\infty\) such that every
canonical first-recovery state with \(0<z<27\) and \(V\ge V_{27}\), under
every choice of one root in each forest component, contains a vertex
\(u\) satisfying

\[
 g(u)\ge\kappa_{27}V.                                \tag{4.1}
\]

Theorem 4.1 is Theorem D.1. Its key reduction is a finite-branch approximation
along an arbitrary variance-divergent canonical sequence. Lemma D.4 rules out
an exposed antichain of
individually negligible descendant variance masses carrying a fixed fraction
of the total variance: such an antichain would produce a Gaussian-mixture
submeasure with positive density at the mean, whereas Lemmas C.4 and C.5 give
\(\sqrt V\,\Pr_z(X=s)\to0\). Lemma D.5 therefore captures, for every fixed
\(\varepsilon>0\), all but \(\varepsilon V\) of the variance on an ancestor-closed
rooted subforest with a bounded number of root-to-leaf branches, retaining the
coefficients of the global martingale. If every vertex contribution were
\(o(V)\), a diagonal choice could let \(\varepsilon\) tend to zero while keeping
the branch count controlled relative to the largest vertex contribution. The
large-displacement estimate would then give
the martingale Lindeberg condition, and the branch-count control gives
concentration of the predictable quadratic variation. The resulting Gaussian
limit, together with the full-domain Fourier estimate, yields a positive
adjacent log-concavity determinant at the mean, contrary to the first-recovery
sign. Thus a large canonical counterexample must instead have a single
macroscopic variance contribution, as asserted in (4.1).

### Theorem 4.2 (occupation and displacement bounds at a dominant vertex)

For every \(c>0\) there are constants \(\rho(c)>0\) and \(V_{\mathrm{bal}}(c)<\infty\)
such that, in every canonical first-recovery state with \(0<z<27\) and
\(V\ge V_{\mathrm{bal}}(c)\), a
vertex satisfying \(g(u)\ge cV\) also satisfies

\[
 p_u\ge\rho(c),
 \qquad 4cV\le\Delta_u^2\le\frac{784}{\rho(c)}V.    \tag{4.2}
\]

The lower bound on \(p_u\) is the substantive part of Theorem C.3. If
\(p_u\to0\) while \(g(u)\ge cV\), then \(\Delta_u^2/V\to\infty\). The recursion
\(\Delta_u=1-\sum_vp_v\Delta_v\), combined with weighted Cauchy--Schwarz,
charges such a large displacement to variance in the children. Lemma C.2
formalizes this charging: if \(b\to\infty\) and \(V/b^2\to0\), the total
variance contribution of vertices with \(|\Delta_x|>b\) is \(o(V)\).
With \(b=|\Delta_u|/2\), both conditions hold, yet \(u\) belongs to this set and
contributes \(g(u)\ge cV\), a contradiction.

Once \(p_u\ge\rho(c)\) is known, the displacement bounds are immediate. The
lower bound follows from \(a_up_uq_u\le1/4\) in (3.1). For the upper bound,
\(a_u,q_u\ge1/28\), while (3.2) gives \(g(u)\le V\); thus
\(a_up_uq_u\ge\rho(c)/784\).

### Theorem 4.3 (size and variance at first recovery)

There are constants \(c_V,C_V,c_N,C_N>0\) and \(V_{\mathrm{sc}}<\infty\) such that
every canonical first-recovery state of a finite forest with \(0<z<27\) and
\(V\ge V_{\mathrm{sc}}\) satisfies

\[
 c_Vs^2\le V\le C_Vs^2,
 \qquad c_Ns\le N\le C_Ns.                           \tag{4.3}
\]

Theorem 4.3 is Theorem C.7.

The quadratic scale in (4.3) is special to a hypothetical first-recovery
state. Lemma C.5 makes the probability of the exact mean exponentially small.
After one bipartition class is revealed, let \(M\) and \(W\) be the conditional
mean and variance of the other class. The proof gives
\(\Pr(W\ge s/112)\ge\delta_*\) for a fixed \(\delta_*>0\). Taking \(H=\gamma s\)
with a sufficiently small fixed \(\gamma>0\), Lemma C.6 shows that
\(\{W\ge4H,\,(M-s)^2\le HW\}\) has probability tending to zero. Thus
\(|M-s|\) is at least a fixed positive multiple of \(s\) with nonvanishing
probability, and the law of total variance gives \(V\gtrsim s^2\). The matching
upper bound follows from \(N=O(s)\) and \(X^2\le NX\).

Lemma C.1 first places every such state of sufficiently large variance in the
range \(3/2<z<27\), by combining the low-activity Gaussian limit with the
local-curvature contradiction. In this range, any
componentwise rooting has at least half of its
vertices with at most one child. Each such vertex has a uniformly positive
global occupation probability, which gives \(N=O(s)\); the reverse inequality
\(s\le N\) is immediate.

Apply Theorem 4.2 with \(c=\kappa_{27}\) and set
\(\rho=\rho(\kappa_{27})\). The immediate consequence of (4.1)--(4.3) is the fixed
linear lower bound

\[
 |\Delta_u|
 \ge \frac{2\sqrt{\kappa_{27}c_V}}{C_N}N
 =:\delta N.                                         \tag{4.4}
\]

## 5. A sublinear bound for the conditional mean difference

The remaining input is local and uses only the rooted recursion. Taking
absolute values in the alternating path expansion reduces the problem to
controlling the total path weight. Bounded activity makes every path product decay geometrically
with depth. At the same time, if the conditional occupation probability at a
vertex is bounded below, the recursion permits only boundedly many children
whose occupation probabilities exceed a fixed threshold. Consequently, for
each threshold only boundedly many descendants can carry a nonnegligible path
weight; every other descendant contributes at most that threshold. Lemma 5.1
makes this observation uniform.

### Lemma 5.1 (sublinear conditional mean difference)

Fix \(0<Z<\infty\) and \(\rho>0\). If \(\rho>Z/(1+Z)\), the class below is empty.
Otherwise, for every \(\varepsilon>0\) there is a finite
constant \(K=K(Z,\rho,\varepsilon)\) such that, for every finite rooted tree,
every \(0<z\le Z\), and every vertex \(u\) with \(p_u\ge\rho\),

\[
 |\Delta_u|\le\varepsilon|T_u|+K.                    \tag{5.1}
\]

Consequently, uniformly over this class,

\[
 \frac{|\Delta_u|}{|T_u|}\longrightarrow0
 \quad\text{as }|T_u|\longrightarrow\infty.         \tag{5.2}
\]

### Proof

The rooted-tree recursion gives

\[
 R_x=z\prod_{y\text{ child of }x}q_y
    =z\prod_y(1-p_y),
 \qquad p_x=\frac{R_x}{1+R_x}.                       \tag{5.3}
\]

Since \(R_x\le z\le Z\),

\[
 0<p_x\le \bar p_Z:=\frac{Z}{1+Z}<1.                \tag{5.4}
\]

Moreover, logarithmic differentiation of (5.3) gives the recursion

\[
 \Delta_x=z\frac{d}{dz}\log R_x
 =1-\sum_{y\text{ child of }x}p_y\Delta_y.           \tag{5.5}
\]

Here \(z\,d\log A_x/dz\) and \(z\,d\log Q_x/dz\) are the conditional mean
occupation counts of \(T_x\) when \(x\) is occupied and absent, respectively.

For \(x\in T_u\), let \(P(u,x)\) be the unique path from \(u\) to \(x\), let
\(d(u,x)\) be its length, and set

\[
 w_u=1,
 \qquad
 w_x=\prod_{x_j\in P(u,x)\setminus\{u\}}p_{x_j},
\]

the product over the nonroot vertices on the path from \(u\) to \(x\).
Induction on subtree height in (5.5) gives the exact finite expansion

\[
 \Delta_u=\sum_{x\in T_u}(-1)^{d(u,x)}w_x.
\]

Therefore

\[
 |\Delta_u|\le W_u:=\sum_{x\in T_u}w_x.             \tag{5.6}
\]

Put \(\ell(t)=-\log(1-t)\). If \(p_x\ge \sigma\), then
\(R_x\ge \sigma/(1-\sigma)\), and (5.3) implies

\[
 \sum_{y\text{ child of }x}\ell(p_y)
 =\log\frac{z}{R_x}
 \le\log\frac{Z(1-\sigma)}{\sigma}.                \tag{5.7}
\]

Fix \(\tau\) with \(0<\tau<\bar p_Z\). Equation (5.7) shows that a vertex with
\(p_x\ge \sigma\) has at most

\[
 M(\sigma,\tau):=
 \left\lceil
  \frac{\log(Z(1-\sigma)/\sigma)}{-\log(1-\tau)}
 \right\rceil                                        \tag{5.8}
\]

children with conditional occupation probability at least \(\tau\). Whenever
\(p_x\ge\sigma\), (5.4) gives \(\sigma\le\bar p_Z\), so the numerator in
(5.8) is nonnegative.

If \(w_x\ge \tau\), every conditional occupation probability on the path
below \(u\) is at least \(\tau\), and
(5.4) gives

\[
 w_x\le \bar p_Z^{d(u,x)}.
\]

Thus \(d(u,x)\le D_\tau\), where

\[
 D_\tau:=\max\{d\in\mathbb Z_{\ge0}:\bar p_Z^d\ge\tau\}<\infty.
\]

At the first generation use (5.8) with \(\sigma=\rho\); at every later
vertex satisfying \(p_x\ge\tau\) use it with \(\sigma=\tau\). Hence the number
of descendants
with \(w_x\ge \tau\), including \(u\), is at most

\[
 K_0=1+M(\rho,\tau)
          \sum_{j=0}^{D_\tau-1}M(\tau,\tau)^j.       \tag{5.9}
\]

Every remaining descendant has weight below \(\tau\). Splitting (5.6) gives

\[
 |\Delta_u|\le W_u\le K_0+\tau|T_u|.                \tag{5.10}
\]

Given \(\varepsilon>0\), choose

\[
 \tau=\min\{\varepsilon/2,\bar p_Z/2\}
\]

and set \(K=K_0(Z,\rho,\tau)\). These choices depend only on
\(Z,\rho,\varepsilon\), so (5.10) proves (5.1) uniformly over the stated class.
Dividing by \(|T_u|\) and letting \(|T_u|\to\infty\) proves (5.2). \(\square\)

## 6. Exclusion of every variance-divergent canonical sequence

Assume that \((F_n,s_n,z_n,V_n)\) is a canonical first-recovery sequence with
\(V_n\to\infty\). Choose one arbitrary root in every component of each
forest. For each sufficiently large \(n\), choose a vertex supplied by
Theorem 4.1 and denote it by \(u_n\). Theorems 4.2 and 4.3 give

\[
 p_{u_n}\ge\rho,
 \qquad |\Delta_{u_n}|\ge\delta N_n.                 \tag{6.1}
\]

Use Lemma 5.1 with \(Z=27\), the fixed occupation constant \(\rho\), and
error tolerance \(\varepsilon=\delta/2\). Let
\(K=K(27,\rho,\delta/2)\) be its constant.
Regard \(T_{u_n}\) as a rooted tree with the parent of \(u_n\) forced absent.
By the definitions in Section 3, its local probabilities \(p_x\) and root mean
difference \(\Delta_{u_n}\) agree with those above. Lemma 5.1 and
\(|T_{u_n}|\le N_n\) now give

\[
 |\Delta_{u_n}|
 \le\frac{\delta}{2}|T_{u_n}|+K
 \le\frac{\delta}{2}N_n+K.                           \tag{6.2}
\]

Since \(0\le X_n\le N_n\), Popoviciu's inequality gives
\(V_n\le N_n^2/4\). Thus \(V_n\to\infty\) implies \(N_n\to\infty\). For
\(N_n>2K/\delta\), the right side of (6.2) is strictly less than \(\delta N_n\),
contradicting (6.1). Therefore:

\[
 \boxed{\text{No canonical first-recovery sequence has }V_n\to\infty.}
                                                               \tag{6.3}
\]

## 7. Eventual unimodality

### Theorem 7.1

There exists \(N_0<\infty\) such that every finite forest \(F\) with
\(|V(F)|\ge N_0\) has a unimodal independence-polynomial coefficient sequence.

### Proof

If no such \(N_0\) existed, there would be nonunimodal forests \(F_n\) with
\(N_n\to\infty\). Let \((F_n,s_n,z_n,V_n)\) be their canonical first-recovery
states. By (2.4), they satisfy \(0<z_n<27\) and
\(V_n\to\infty\), contradicting (6.3). \(\square\)

### Corollary 7.2 (connected trees)

There exists \(N_0<\infty\) such that every finite connected tree \(T\) with
\(|V(T)|\ge N_0\) has a unimodal independence-polynomial coefficient
sequence.

*Proof.* Every finite connected tree is a finite forest, so this is the
special case of Theorem 7.1 with one component. \(\square\)

## 8. Remaining finite cases

Theorem 7.1 reduces the full finite-forest problem to finitely many orders.
Indeed, (6.3) shows that the variance of every canonical first-recovery counterexample is
bounded by some finite constant \(V_0\). Proposition 2.1 then implies

\[
 N\le64\cdot28^8V_0^2.                               \tag{8.1}
\]

The constant \(V_0\) obtained above is not explicit, so (8.1) is not currently
computationally effective and the remaining orders are not verified here. Thus
the full forest conjecture, and likewise its connected-tree case, is reduced to
a finite problem whose order bound is presently ineffective. The conclusion concerns
unimodality; log-concavity is known to fail even for trees.

# Statement on AI-assisted research

During the development of this work, the author relied extensively on
large language model (LLM) systems to explore proof strategies,
assist with drafting and the critique of arguments, and generate Lean 4
formalizations of selected arguments. The systems used included an
author-developed LLM research system, the GPT-5.6 Pro web interface, and
OpenAI Codex. The author
takes responsibility for the statements, proofs, citations, and final
presentation in this manuscript. A separate companion document describing the
AI-assisted development of the proof and its intermediate lemmas is in
preparation.

# Appendix A. Uniform Fourier decay for finite forests

This appendix proves the Fourier envelope used in (B.6) and (D.21), uniformly over all
finite forests, all degrees and depths, and all activities in a fixed bounded
interval. It also records a weighted Fourier-tail consequence for triangular
arrays of independent forest components. Every
boundary-conditioned partition function and descendant subtree used below is
obtained by deleting vertices from the original forest. The two results are
the pointwise envelope (A.3) and the aggregate tail estimate (A.5).

The proof of the pointwise envelope has two principal stages. Lemma A.8
separates the contraction along a decorated path into a side-forest
modulus--phase estimate, phase control from two consecutive rows, and a
summation of relative decrements. Lemma A.9 then embeds that path estimate in
a recursive maximal-modulus decomposition. Lemma A.10 records termination,
disjointness, and
the absence of repeated losses in the final strong induction.

## A.1. Statement and notation

For a finite forest \(F\), let

\[
 I_F(w)=\sum_{J\subseteq V(F)}w^{|J|}
       \mathbf 1_{\{J\text{ is independent in }F\}}
\]

be its independence polynomial.  At activity \(z>0\), the hard-core law is

\[
 \Pr_{F,z}(J)=\frac{z^{|J|}}{I_F(z)}
 \mathbf 1_{\{J\text{ is independent in }F\}}.
 \tag{A.1}
\]

Write \(X_{F,z}=|J|\), \(\mu_{F,z}=\mathbb E X_{F,z}\), and
\(V_{F,z}=\operatorname{Var}X_{F,z}\).  Its centered characteristic function,
modulus, and logarithmic loss are

\[
 \phi_{F,z}(\theta)
   =\mathbb E e^{\mathrm i\theta(X_{F,z}-\mu_{F,z})},\qquad
 M_{F,z}(\theta)=|\phi_{F,z}(\theta)|,\qquad
 \ell_{F,z}(\theta)=-\log M_{F,z}(\theta),
 \tag{A.2}
\]

where \(-\log0=+\infty\).  Centering does not change the modulus, and hence

\[
 M_{F,z}(\theta)=\frac{|I_F(ze^{\mathrm i\theta})|}{I_F(z)}.
\]

When \(F\) is empty, \(V_{F,z}=0\), \(M_{F,z}=1\), and all assertions below
hold trivially.

**Theorem A.1 (full-domain Fourier envelope).**  For every \(Z<\infty\) with
\(Z>0\), there are constants \(c_Z>0\) and
\(\alpha_Z\in(0,1)\) such that, for every finite forest \(F\), every
\(0<z\le Z\), and every \(|\theta|\le\pi\),

\[
 \boxed{
 \ell_{F,z}(\theta)
 \ge c_Z\min\left\{V_{F,z}\theta^2,
                   (V_{F,z}\theta^2)^{\alpha_Z}\right\}.}
 \tag{A.3}
\]

In particular, after changing \(c_Z\),

\[
 \ell_{F,z}(\theta)\ge c_Z\log(1+V_{F,z}\theta^2).
 \tag{A.4}
\]

The following consequence is not needed in the main proof, but records the
corresponding aggregate tail estimate.

**Corollary A.2 (weighted aggregate Fourier tail).**  For each \(n\), let
\(X_{n,1},\ldots,X_{n,m_n}\) be independent hard-core counts on finite
forests \(F_{n,1},\ldots,F_{n,m_n}\), all at a common activity
\(0<z_n\le Z\).  Put

\[
 v_{n,j}=\operatorname{Var}X_{n,j},\qquad
 W_n=\sum_jv_{n,j},
\]

and let

\[
 \Phi_n(\theta)=\prod_j\phi_{F_{n,j},z_n}(\theta)
\]

be the centered characteristic function of their sum. If \(W_n\to\infty\),
then

\[
 \boxed{
 \lim_{R\to\infty}\limsup_{n\to\infty}
 \int_{R\le |u|\le\pi\sqrt{W_n}}
 (1+u^2)\left|\Phi_n\!\left(\frac{u}{\sqrt{W_n}}\right)\right|\,du=0.}
 \tag{A.5}
\]

The rest of the appendix proves the theorem and its corollary.

## A.2. Rooted martingale increments and a uniform fourth moment

Root every tree component of \(F\).  For a vertex \(v\), let \(T_v\) be the
full descendant subtree rooted at \(v\), and let \(\operatorname{ch}(v)\) be
its children.  Conditional on the parent of \(v\) being unoccupied, define

\[
 b_v=\Pr(v\text{ is occupied}),\qquad q_v=1-b_v.
\]

The root of a component is understood to have a virtual unoccupied parent.
Deleting the root of \(T_v\) gives the exact recursion

\[
 \frac{b_v}{q_v}=z\prod_{u\in\operatorname{ch}(v)}q_u.
 \tag{A.7}
\]

Consequently, with

\[
 \underline q_Z=(1+Z)^{-1},\qquad \overline p_Z=\frac{Z}{1+Z}=1-\underline q_Z,
\]

one has, uniformly in \(F,z\), and \(v\),

\[
 q_v\ge\underline q_Z,\qquad b_v\le\overline p_Z<1.
 \tag{A.8}
\]

Let \(m_v^0\) and \(m_v^1\) be the mean occupation count in \(T_v\),
conditional respectively on \(v\) being absent and occupied, and put

\[
 d_v=m_v^1-m_v^0.
\]

Conditioning on \(v\), and then on the child roots, gives

\[
 d_v=1-\sum_{u\in\operatorname{ch}(v)}b_ud_u.
 \tag{A.9}
\]

The following estimate is the moment input for the central Fourier range.

**Lemma A.3 (uniform fourth moment).**  For every finite \(Z\) there is
\(C_Z^{(4)}<\infty\) such that every finite forest and every \(0<z\le Z\)
satisfy

\[
 \mathbb E|X_{F,z}-\mu_{F,z}|^4
 \le C_Z^{(4)}V_{F,z}(1+V_{F,z}).
 \tag{A.10}
\]

**Proof.**  Introduce independent Bernoulli variables \(B_v\), one at each
vertex, with \(\Pr(B_v=1)=b_v\).  Starting at the component roots, define the
availability indicator \(R_v\) and the occupation indicator \(\xi_v\)
by

\[
 R_v=1\quad\text{at a component root},\qquad
 R_v=1-\xi_{\operatorname{par}(v)}\quad\text{otherwise},\qquad
 \xi_v=R_vB_v.
\]

Induction from the leaves, using (A.7), shows that
\((\xi_v)_{v\in F}\) has exactly the hard-core law (A.1).  Order the vertices
so that each parent precedes its children and reveal the \(B_v\)'s in that
order.  The corresponding Doob increment is

\[
 D_v=R_vd_v(B_v-b_v).
 \tag{A.11}
\]

Indeed, if \(R_v=0\), the Bernoulli variable \(B_v\) has no effect. If \(R_v=1\),
changing \(B_v\) changes the conditional expected count in \(T_v\) from
\(m_v^0\) to \(m_v^1\), a difference of \(d_v\).  Thus

\[
 X_{F,z}-\mu_{F,z}=\sum_{v\in F}D_v.
 \tag{A.12}
\]

Set

\[
 e_v=b_vq_vd_v^2,\qquad A=\sum_ve_v,\qquad w_v=\mathbb ER_v.
\]

Every component root has \(w_v=1\).  At a nonroot vertex, its parent has
marginal occupation probability at most \(\overline p_Z\), so \(w_v\ge\underline q_Z\).
Orthogonality of the martingale increments therefore gives the exact variance
identity

\[
 V_{F,z}=\sum_vw_ve_v,
 \qquad \underline q_Z A\le V_{F,z}\le A.
 \tag{A.13}
\]

The predictable quadratic sum is

\[
 H=\sum_v\mathbb E(D_v^2\mid\mathcal F_{v^-})
   =\sum_vR_ve_v.
\]

Since \(0\le H\le A\) and \(\mathbb EH=V_{F,z}\),

\[
 \mathbb EH^2\le A\mathbb EH\le\underline q_Z^{-1}V_{F,z}^2.
 \tag{A.14}
\]

It remains to control the fourth moments of the individual increments. For each
vertex set

\[
 s_v=\sum_{u\in\operatorname{ch}(v)}b_u,\qquad
 t_v=\sum_{u\in\operatorname{ch}(v)}b_ud_u^2,\qquad
 r_v=\sum_{u\in\operatorname{ch}(v)}b_ud_u.
\]

From (A.7), \(q_u\le e^{-b_u}\), and (A.8),

\[
 b_v\le Ze^{-s_v},\qquad
 t_v\le\underline q_Z^{-1}\sum_{u\in\operatorname{ch}(v)}e_u,\qquad
 r_v^2\le s_vt_v.
 \tag{A.15}
\]

If \(|d_v|\le2\), then \(b_vq_vd_v^4\le4e_v\).  If \(|d_v|>2\),
(A.9) implies \(|r_v|\ge|d_v|/2\), and hence

\[
 \begin{aligned}
 b_vq_vd_v^4
 &\le16b_vr_v^4
 \le16Ze^{-s_v}s_v^2t_v^2\\
 &\le64Ze^{-2}\underline q_Z^{-2}
 \left(\sum_{u\in\operatorname{ch}(v)}e_u\right)^2.
 \end{aligned}
 \tag{A.16}
\]

Here \(\sup_{s\ge0}s^2e^{-s}=4e^{-2}\).  Child sets belonging to distinct
vertices are disjoint, so, with \(C_{\mathrm A}=64Ze^{-2}\underline q_Z^{-2}\),

\[
 \sum_vb_vq_vd_v^4\le4A+C_{\mathrm A}A^2.
 \tag{A.17}
\]

For completeness, we record the finite martingale estimate used to combine
these bounds.  If \(D_1,\ldots,D_N\) are real martingale differences,

\[
 h_k=\mathbb E(D_k^2\mid\mathcal F_{k-1}),\qquad
 H=\sum_kh_k,
\]

then

\[
 \mathbb E\left|\sum_kD_k\right|^4
 \le\left(\frac{128}{9}\right)^2\mathbb EH^2
      +6\sum_k\mathbb ED_k^4.
 \tag{A.18}
\]

To prove (A.18), write \(S_k=\sum_{j\le k}D_j\) and
\(c_k=\mathbb E(D_k^3\mid\mathcal F_{k-1})\).  Conditional expansion and
\(|c_k|\le(h_k\mathbb E(D_k^4\mid\mathcal F_{k-1}))^{1/2}\) give

\[
 \mathbb E(S_k^4-S_{k-1}^4\mid\mathcal F_{k-1})
 \le8S_{k-1}^2h_k+3\mathbb E(D_k^4\mid\mathcal F_{k-1}).
\]

After summation, if \(S_*=\max_{k\le N}|S_k|\) and
\(G=\sum_k\mathbb ED_k^4\), Cauchy--Schwarz gives

\[
 \mathbb ES_N^4
 \le8\mathbb E(S_*^2H)+3G
 \le8(\mathbb ES_*^4)^{1/2}(\mathbb EH^2)^{1/2}+3G.
\]

We use the finite Doob inequality

\[
 \mathbb E\max_{k\le N}|S_k|^4
 \le\left(\frac43\right)^4\mathbb E|S_N|^4
\]

whose proof is included next.  Apply the first-crossing argument to the nonnegative
submartingale \(|S_k|\).  For \(\lambda>0\), its first-crossing time gives

\[
 \lambda\Pr\!\left(\max_k|S_k|>\lambda\right)
 \le \mathbb E\!\left[
 |S_N|\mathbf 1_{\{\max_k|S_k|>\lambda\}}\right].
\]

Integrating this inequality and using Hölder's inequality proves the displayed
maximal estimate: multiplication by \(4\lambda^2\), integration over
\(\lambda>0\), and Fubini's theorem give

\[
 \mathbb E\max_{k\le N}|S_k|^4
 \le\frac43\mathbb E\!\left[
 |S_N|\max_{k\le N}|S_k|^3\right].
\]

Hölder's inequality then gives

\[
 \left(\mathbb E\max_{k\le N}|S_k|^4\right)^{1/4}
 \le\frac43(\mathbb E|S_N|^4)^{1/4}.
\]

Substitution in the bound for \(\mathbb ES_N^4\) gives

\[
 \mathbb ES_N^4
 \le\frac{128}{9}(\mathbb ES_N^4)^{1/2}
                  (\mathbb EH^2)^{1/2}+3G.
\]

Applying \(ab\le(a^2+b^2)/2\) to the product on the right and moving
\(\frac12\mathbb ES_N^4\) to the left proves (A.18).

For a Bernoulli variable of mean \(b\),

\[
 \mathbb E(B-b)^4=b(1-b)(b^3+(1-b)^3)\le b(1-b).
\]

Thus (A.17) bounds \(\sum_v\mathbb ED_v^4\).  Combining (A.13),
(A.14), (A.17), and (A.18) gives

\[
 \mathbb E|X_{F,z}-\mu_{F,z}|^4
 \le \frac{24}{\underline q_Z}V_{F,z}
 +\left\{\frac1{\underline q_Z}\left(\frac{128}{9}\right)^2
        +\frac{6C_{\mathrm A}}{\underline q_Z^2}\right\}V_{F,z}^2,
\]

which is (A.10).  Every constant depends only on \(Z\).  \(\square\)

## A.3. Characteristic-function bounds

We next prove a full-frequency estimate which rules out exact or approximate
lattice concentration at any fixed nonzero frequency.

**Lemma A.4 (uniform characteristic-function gap).** Let

\[
 \kappa_Z=\min\left\{
 \frac{1-e^{-7/16}}8,\frac1{8(1+Z)}\right\}.
\]

For every finite forest \(F\), \(0<z\le Z\), and \(|\theta|\le\pi\),

\[
 \ell_{F,z}(\theta)
 \ge\kappa_Z\min\{V_{F,z},1\}\sin^2(\theta/2).
 \tag{A.19}
\]

**Proof.**  A forest is bipartite; fix a bipartition
\(V(F)=L\sqcup R\).  Put

\[
 p=\frac{z}{1+z},\qquad q=p(1-p),\qquad
 h=\sin^2(\theta/2),\qquad
 a=1-p+pe^{\mathrm i\theta},\qquad
 r=|a|=\sqrt{1-4qh}.
\]

The empty forest was disposed of in Section A.1, so assume \(F\) is
nonempty.

For an independent set \(J\), let

\[
 A_L(J)=|\{x\in L:N(x)\cap J=\varnothing\}|,
\]

and define \(A_R\) analogously.  Conditional on \(J\cap R\), the available
vertices in \(L\) are independent Bernoulli variables of mean \(p\).  Hence

\[
 |\phi_{F,z}(\theta)|\le\mathbb Er^{A_L},
 \qquad
 |\phi_{F,z}(\theta)|\le\mathbb Er^{A_R}.
 \tag{A.20}
\]

Suppose first that \(p\ge1/8\).  Pointwise \(A_L+A_R\ge1\), and for
nonnegative integers \(a_0,b_0\) with \(a_0+b_0\ge1\),
\(r^{a_0}+r^{b_0}\le1+r\).  Averaging the two bounds in (A.20) gives

\[
 |\phi_{F,z}(\theta)|\le\frac{1+r}{2}
 \le1-p(1-p)h
 \le\exp\left\{-\frac{h}{8(1+Z)}\right\}.
 \tag{A.21}
\]

This is stronger than (A.19) in this case.

Now suppose that \(p\le1/8\), and put \(n=|V(F)|\), \(A=A_L+A_R\), and
\(U=n-A\).  Every unavailable vertex has an occupied neighbor, so

\[
 U\le\sum_{x\in J}\deg(x).
\]

For every vertex \(x\), deletion of \(x\) gives

\[
 \Pr(x\in J)
 =\frac{zI_{F-N[x]}(z)}{I_{F-x}(z)+zI_{F-N[x]}(z)}\le p.
\]

Since a forest has at most \(n\) edges,
\(\mathbb EU\le2pn\).  Markov's inequality therefore gives
\(\Pr(A\ge n/2)\ge1/2\).  On this event at least one of \(A_L,A_R\) is at
least \(n/4\); consequently one fixed side \(S\in\{L,R\}\) satisfies

\[
 \Pr(A_S\ge n/4)\ge\frac14.
\]

Using this event in (A.20), rather than applying Jensen's inequality, yields

\[
 |\phi_{F,z}(\theta)|
 \le1-\frac14(1-r^{n/4}).
 \tag{A.22}
\]

Since \(r\le e^{-2p(1-p)h}\), if \(t=np\), then

\[
 r^{n/4}\le e^{-7th/16}.
\]

Concavity of \(1-e^{-7x/16}\) on \([0,1]\), followed by monotonicity when
\(t\ge1\), gives

\[
 1-e^{-7th/16}\ge(1-e^{-7/16})\min\{t,1\}h.
 \tag{A.23}
\]

It remains to compare \(t\) with the variance.  For distinct vertices
\(x,y\), either they are adjacent and cannot both be occupied, or conditioning
on \(x\in J\) leaves a hard-core law on \(F-N[x]\), in which the marginal
occupation probability of \(y\) is at most \(p\).  Thus

\[
 V_{F,z}\le\mathbb EX_{F,z}^2
 \le np+n(n-1)p^2\le t+t^2.
\]

It follows that

\[
 \min\{t,1\}\ge\frac12\min\{V_{F,z},1\}.
 \tag{A.24}
\]

Combining (A.22)--(A.24) with \(1-y\le e^{-y}\) proves (A.19) in the
low-\(p\) case.  \(\square\)

The fourth-moment estimate and Lemma A.4 now give the small-frequency
curvature needed later.

**Lemma A.5 (small-frequency curvature).**  For every finite \(Z\) there
are \(x_Z^{\mathrm c}>0\) and \(c_Z^{\mathrm c}>0\) such that

\[
 V_{F,z}\theta^2\le x_Z^{\mathrm c},\quad |\theta|\le\pi
 \quad\Longrightarrow\quad
 \ell_{F,z}(\theta)\ge c_Z^{\mathrm c}V_{F,z}\theta^2
 \tag{A.25}
\]

for every finite forest and every \(0<z\le Z\).

**Proof.**  Put \(V=V_{F,z}\), \(x=V\theta^2\), and let \(X'\) be an
independent copy of \(X=X_{F,z}\).  If \(V\le1\), Lemma A.4 and
\(\sin^2(\theta/2)\ge\theta^2/\pi^2\) give

\[
 \ell_{F,z}(\theta)\ge\frac{\kappa_Z}{\pi^2}x.
\]

Suppose \(V\ge1\).  With \(Y=X-X'\), Lemma A.3 gives

\[
 \mathbb EY^4
 =2\mathbb E|X-\mathbb EX|^4+6V^2
 \le(4C_Z^{(4)}+6)V^2.
\]

Because \(1-\cos t\ge t^2/2-t^4/24\) for every real \(t\),

\[
 \begin{aligned}
 1-M_{F,z}(\theta)^2
 &=\mathbb E[1-\cos(\theta Y)]\\
 &\ge x-\frac{4C_Z^{(4)}+6}{24}x^2.
 \end{aligned}
 \tag{A.26}
\]

Choose

\[
 x_Z^{\mathrm c}
 =\min\left\{1,\frac{12}{4C_Z^{(4)}+6}\right\}.
\]

Then the right side of (A.26) is at least \(x/2\).  Finally,
\(-\log r\ge(1-r^2)/2\) for \(0<r\le1\), so
\(\ell_{F,z}(\theta)\ge x/4\).  Taking

\[
 c_Z^{\mathrm c}=\min\left\{\frac14,
                                  \frac{\kappa_Z}{\pi^2}\right\}
\]

proves the assertion.  \(\square\)

## A.4. Root variance comparison and bounded-scale compactness

We first collect the rooted variance identities.  Let \(T\) be a rooted tree,
let \(r\) be its root, and set

\[
 Q=T-r,\qquad R=T-N[r].
\]

Thus \(Q\) is the forest of descendant subtrees rooted at the children of
\(r\), and \(R\) is the forest
obtained by also deleting every child root.  Write \(b=b_r\), \(q=1-b\),
and let \(d=d_r\).  From this point through Section A.6, an omitted activity
subscript always means the same fixed activity \(z\); for example,
\(V_T=V_{T,z}\), \(M_T=M_{T,z}(\theta)\), and
\(\ell_T=\ell_{T,z}(\theta)\).  Conditional variance at the root gives

\[
 V_T=qV_Q+bV_R+bqd^2.
 \tag{A.27}
\]

For the child roots \(u\), put

\[
 E=\sum_ub_uq_ud_u^2,\qquad R_0=\sum_u\frac{b_u}{q_u}.
\]

Weighted Cauchy--Schwarz and (A.9) give
\((1-d)^2\le R_0E\).  Moreover,

\[
 bR_0\le Z,
 \tag{A.28}
\]

because

\[
 \left(\prod_uq_u\right)\sum_u\frac{b_u}{q_u}
 =\sum_ub_u\prod_{w\ne u}q_w\le1
\]

and \(b/q=z\prod_uq_u\).  Since \(E\le V_Q\), (A.27)--(A.28) imply,
with

\[
 A_Z=1+3Z,\qquad B_Z=1+Z,
\]

the depth-free root estimates

\[
 qV_Q\le V_T\le A_ZV_Q+2b,
 \qquad V_R\le B_ZV_Q.
 \tag{A.29}
\]

Indeed, \(bqd^2\le2b+2ZV_Q\), while
\(bV_R\le ZV_Q\).  Applying the first upper bound in (A.29) to every child
subtree and summing also gives

\[
 V_Q\le A_ZV_R+2L,
 \qquad
 L=\log\frac{I_Q(z)}{I_R(z)}
   =\sum_u-\log q_u.
 \tag{A.30}
\]

The next lemma is the bounded-scale compactness statement required in the
global induction.  Its proof is included because ordinary compactness of a
fixed family of polynomials would not be uniform in forest size or depth.

**Lemma A.6 (bounded-scale compactness).**  For every \(Z<\infty\) and every
\(0<a\le b<\infty\), there is
\(\varepsilon=\varepsilon(Z,a,b)>0\) such that

\[
 a\le V_{F,z}\theta^2\le b,\quad |\theta|\le\pi
 \quad\Longrightarrow\quad
 \ell_{F,z}(\theta)\ge\varepsilon
 \tag{A.31}
\]

for every finite forest and every \(0<z\le Z\).

**Proof.**  We first prove a one-edge modulus transfer.  Root a tree \(T\),
and let \(U=T_v\) be any descendant subtree. If \(U\ne T\), let \(s\) be the
parent of its root.  Under the hard-core law on \(T\),

\[
 w:=\Pr(s\text{ is unoccupied})
 =\frac{I_{T-s}(z)}{I_T(z)}\ge\frac1{1+z}\ge\underline q_Z,
 \tag{A.32}
\]

because \(T-N[s]\) is an induced subgraph of \(T-s\).  Conditional on this
event, the law on \(U\) is its free hard-core law and is independent of the
outside configuration.  Splitting the characteristic function according to
the event and using the triangle inequality yields

\[
 1-M_{U,z}(\theta)
 \le\underline q_Z^{-1}(1-M_{T,z}(\theta)).
 \tag{A.33}
\]

Only the immediate outside endpoint is conditioned; no factor depending on
the depth of \(U\) appears.

Suppose that (A.31) fails.  There are \(F_j,z_j,\theta_j\) in the stated
range such that

\[
 a\le\theta_j^2V_{F_j,z_j}\le b,
 \qquad M_{F_j,z_j}(\theta_j)\longrightarrow1.
 \tag{A.34}
\]

After passing to a subsequence, either \(|\theta_j|\ge\delta>0\), in which
case Lemma A.4 gives a fixed positive loss, or \(\theta_j\to0\).  We treat
the latter case.

Write \(F_j\) as the disjoint union of its tree components and put
\(x_{j,i}=\theta_j^2V_{j,i}\).  By Lemma A.5 and additivity of logarithmic
loss,

\[
 \sum_{i:x_{j,i}\le x_Z^{\mathrm c}}x_{j,i}\longrightarrow0.
\]

There are at most \(b/x_Z^{\mathrm c}\) remaining components.  Hence one can
select a tree component \(T_j\) and a constant \(a_1>0\), depending only on
\(Z,a,b\), so that

\[
 a_1\le\theta_j^2V_{T_j,z_j}\le b,
 \qquad M_{T_j,z_j}(\theta_j)\longrightarrow1.
 \tag{A.35}
\]

Set \(r_0=\min\{x_Z^{\mathrm c},a_1/2\}\).  We claim that, for all large
\(j\), every descendant subtree \(U\subseteq T_j\) with

\[
 \theta_j^2V_{U,z_j}>r_0
 \tag{A.36}
\]

has a descendant subtree rooted at one of its children that satisfies the
same inequality. Let
\(Q_U=U-\operatorname{root}(U)\).  By (A.29), uniformly in \(U\),

\[
 \theta_j^2V_{Q_U,z_j}\ge\frac{r_0}{2A_Z}
 \tag{A.37}
\]

once \(\theta_j^2\le r_0/4\).  Conditioning the root of \(U\) to be absent,
and then applying (A.33) directly from \(T_j\) to \(U\), gives

\[
 1-M_{Q_U,z_j}(\theta_j)
 \le\underline q_Z^{-2}(1-M_{T_j,z_j}(\theta_j))\longrightarrow0,
 \tag{A.38}
\]

uniformly over all such \(U\).  If every child component \(W\) of \(Q_U\)
had \(\theta_j^2V_W\le r_0\), Lemma A.5 and independence would give

\[
 \ell_{Q_U,z_j}(\theta_j)
 \ge c_Z^{\mathrm c}\theta_j^2V_{Q_U,z_j}
 \ge\frac{c_Z^{\mathrm c}r_0}{2A_Z},
\]

contradicting (A.38).  The claim follows.

Starting from (A.35), the claim produces a strict descending chain of full
descendant subtrees inside the same finite tree \(T_j\), each satisfying (A.36).
The chain must end at a leaf.  A one-vertex tree has variance at most \(1/4\),
so its scaled variance is less than \(r_0\) for all large \(j\), a
contradiction.  Thus (A.31) holds.  \(\square\)

Combining Lemmas A.5 and A.6, for every fixed \(X_0<\infty\) and every
\(\alpha\in(0,1)\), there is \(c=c(Z,X_0,\alpha)>0\) such that

\[
 \ell_{F,z}(\theta)\ge cH_\alpha(V_{F,z}\theta^2),
 \qquad V_{F,z}\theta^2\le X_0,
 \qquad H_\alpha(x)=\min\{x,x^\alpha\}.
 \tag{A.39}
\]

## A.5. Variance and Fourier contraction along a path

We now establish the depth-free estimates used when the scaled variance is
unbounded.

**Lemma A.7 (variance bound along a path).** Let
\(v_0,v_1,\ldots,v_L\), \(L\ge1\), be a downward path in a rooted tree, and let
\(S_k\) be the set of children of \(v_k\) other than \(v_{k+1}\).  Let
\(\mathcal B_k=\bigsqcup_{u\in S_k}T_u\) be their side forest.  Then

\[
 V_{T_{v_0},z}\le C_Z\left\{
 \sum_{k=0}^{L-1}b_{v_k}+V_{T_{v_L},z}
 +\sum_{k=0}^{L-1}V_{\mathcal B_k,z}\right\},
 \tag{A.40}
\]

where \(C_Z\) is independent of \(L\).

**Proof.**  Write \(b_k=b_{v_k}\), \(d_k=d_{v_k}\),
\(e_k=b_kq_kd_k^2\), and

\[
 c_k=\sum_{u\in S_k}b_ud_u,\qquad
 E_k=\sum_{u\in S_k}b_uq_ud_u^2,\qquad
 P_0=1,\quad P_k=\prod_{r=1}^kb_r.
\]

Iteration of \(d_k=1-b_{k+1}d_{k+1}-c_k\) gives

\[
 |d_0|\le\sum_{k<L}P_k+\sum_{k<L}P_k|c_k|+P_L|d_L|.
\]

The first sum is at most \(\underline q_Z^{-1}\).  If
\(R_k=\sum_{u\in S_k}b_u/q_u\), then
\(c_k^2\le R_kE_k\), while the occupation-probability identity gives
\(b_kR_k\le Z\),
exactly as in (A.28).  A second weighted Cauchy--Schwarz inequality gives

\[
 \left(\sum_{k<L}P_k|c_k|\right)^2
 \le\left(\sum_{k<L}P_k\right)
     \left(\sum_{k<L}P_kR_kE_k\right)
 \le\underline q_Z^{-1}\sum_{k<L}P_kR_kE_k.
\]

For \(k=0\), \(b_0P_0R_0\le Z\).  For \(k\ge1\),

\[
 b_0P_kR_k=b_0P_{k-1}b_kR_k
 \le Z\overline p_Z^{k-1}.
\]

The bottom term satisfies

\[
 b_0P_L^2d_L^2
 =b_0P_{L-1}^2\frac{b_L}{q_L}e_L
 \le Z\overline p_Z^{2L-1}e_L.
\]

Using \(e_0\le b_0d_0^2\) and
\((r+s+t)^2\le3(r^2+s^2+t^2)\), we obtain

\[
 e_0\le C_Z\left\{b_0+
 \sum_{k<L}\overline p_Z^{\max\{k-1,0\}}E_k+
 \overline p_Z^{2L-1}e_L\right\}.
 \tag{A.41}
\]

Apply (A.41) to every suffix \(v_r,\ldots,v_L\).  Each \(E_k\) receives total
weight at most

\[
 2+\sum_{j\ge1}\overline p_Z^j<\infty,
\]

and the bottom term receives another bounded geometric weight. Finally,
the variance identity (A.13), applied inside each disjoint side or bottom
descendant subtree, bounds the sum of its \(e_v\)'s by \(\underline q_Z^{-1}\) times
its variance. Adding the path, side, and bottom contributions proves (A.40).
\(\square\)

We next prove the Fourier analogue of (A.40).  Let
\(v_0,\ldots,v_L\) be a downward path.  At \(v_k\), let
\(\mathcal S_k\) be the side forest, and write
\(\operatorname{Comp}(\mathcal S_k)\) for its set of tree components.
Define

\[
 A_k(w)=I_{\mathcal S_k}(w),\qquad
 C_k(w)=\prod_{U\in\operatorname{Comp}(\mathcal S_k)}
             I_{U-\operatorname{root}(U)}(w),
\]

\[
 a_k=\frac{A_k(ze^{\mathrm i\theta})}{A_k(z)},\qquad
 c_k=\frac{C_k(ze^{\mathrm i\theta})}{C_k(z)},\qquad
 \Lambda_k=-\log\prod_{U\in\operatorname{Comp}(\mathcal S_k)}(1-b_U).
 \tag{A.42}
\]

Here \(b_U\) is the occupation probability of the root of \(U\) in its free
law.  Empty products equal one.  We also write
\(b_k=b_{v_k}\), \(q_k=1-b_k\), and \(e_1=(1,0)^{\mathsf T}\).  When
\(a_kc_k\ne0\), define

\[
 \gamma_k=\arg(e^{\mathrm i\theta}c_k/a_k)
 \quad\text{in }\mathbb R/(2\pi\mathbb Z).
\]

If \(a_kc_k=0\), set \(\gamma_k=0\); in that case every later occurrence of
its phase term is bounded by the corresponding radial defect and the chosen
value is immaterial.

**Lemma A.8 (transfer-matrix contraction along a decorated path).** There are
constants \(c_Z,C_Z>0\) such that, for every path as above and every complex bottom vector
\(f_L\in\mathbb C^2\) whose coordinate moduli are at most one,

\[
 \left|e_1^{\mathsf T}K_0K_1\cdots K_{L-1}f_L\right|
 \le C_Z\exp\left\{-c_Z\sin^2(\theta/2)
        \sum_{k<L}(b_k+\Lambda_k)\right\},
 \tag{A.43}
\]

where

\[
 K_k=
 \begin{pmatrix}
 q_ka_k&b_ke^{\mathrm i\theta}c_k\\
 a_k&0
 \end{pmatrix}.
 \tag{A.44}
\]

The constants are independent of the path length, the side forests, and the
bottom subtree.

**Proof.** We first prove the phase restriction imposed by a side
forest.  Attach a new root to the roots of the components of an arbitrary
side forest \(S\), and let \(\bar b\) and \(\bar q=1-\bar b\) be the new
root's occupation and vacancy probabilities.  With

\[
 a=\frac{I_S(ze^{\mathrm i\theta})}{I_S(z)},\qquad
 c=\frac{\prod_UI_{U-\operatorname{root}(U)}(ze^{\mathrm i\theta})}
          {\prod_UI_{U-\operatorname{root}(U)}(z)},
\]

the normalized uncentered characteristic function of the resulting tree is

\[
 \bar q a+\bar b e^{\mathrm i\theta}c.
 \tag{A.45}
\]

Put \(h=\sin^2(\theta/2)\), \(r=|a|\), and \(s=|c|\). When
\(a,c\ne0\), let

\[
 \gamma=\arg(e^{\mathrm i\theta}c/a)
       \quad\text{in }\mathbb R/(2\pi\mathbb Z),
\]

and set \(\gamma=0\) otherwise.

**Sublemma A.8.1 (side-forest radial and phase coercivity).** With the
quantities above, the radial defects and the relative phase satisfy (A.48).
When \(a=0\) or \(c=0\), the phase term is omitted and the corresponding
radial defect controls the estimate.

*Proof.*

Its variance is bounded below by \(\underline q_Z^2\bar b\).  To see this, use the
notation \(d,E,R_0\) preceding (A.28). The root and child-root martingale
increments in (A.13) give

\[
 V\ge\bar b\bar qd^2+\underline q_Z E
 \ge\underline q_Z\bar b\left(d^2+\frac1Z(1-d)^2\right)
 \ge\underline q_Z^2\bar b.
 \tag{A.46}
\]

The childless case follows directly from
\(V=\bar b\bar q\ge\underline q_Z\bar b\).  Lemma A.4 and (A.46) imply

\[
 1-|\bar q a+\bar b e^{\mathrm i\theta}c|
 \ge c_Z\bar b h.
 \tag{A.47}
\]

If \(\operatorname{dist}(\gamma,2\pi\mathbb Z)\) denotes its representative
in \([0,\pi]\), rationalizing the triangle deficit gives

\[
 \begin{aligned}
 1-|\bar q a+\bar b e^{\mathrm i\theta}c|
 \le{}&\bar q(1-r)+\bar b(1-s)\\
 &+\frac{\bar b}{2}
   \operatorname{dist}(\gamma,2\pi\mathbb Z)^2.
 \end{aligned}
\]

When \(a=0\) or \(c=0\), the corresponding radial defect controls the whole
estimate. Combining this bound with (A.47) gives the side constraint

\[
 \bar b h\le C_Z\left\{(1-r)+\bar b(1-s)
 +\bar b\operatorname{dist}(\gamma,2\pi\mathbb Z)^2\right\}.
 \tag{A.48}
\]

\(\square\)

We now turn to the matrix product.  The polynomial recursions along the path
are

\[
 \begin{aligned}
 I_{T_{v_k}}(w)
 &=A_k(w)I_{T_{v_{k+1}}}(w)
   +wC_k(w)I_{T_{v_{k+1}}-v_{k+1}}(w),\\
 I_{T_{v_k}-v_k}(w)&=A_k(w)I_{T_{v_{k+1}}}(w).
 \end{aligned}
\]

After normalization at \(w=z\), these recursions are exactly (A.44).
Coefficient positivity gives the coordinatewise bound on every bottom
vector.

Starting with \((x_0,y_0)=(1,0)\), set

\[
 (x_{k+1},y_{k+1})=(x_k,y_k)K_k,\qquad
 N_k=|x_k|+|y_k|.
\]

Then \(N_k\) is nonincreasing.  More precisely, if

\[
 \Delta_k=N_k-N_{k+1},\qquad
 D_k=q_k|x_k|+|y_k|-|q_kx_k+y_k|,
\]

then

\[
 \Delta_k=D_k+(1-|a_k|)|q_kx_k+y_k|
              +b_k(1-|c_k|)|x_k|.
 \tag{A.49}
\]

**Sublemma A.8.2 (phase control from two consecutive rows).** Whenever
\(k+1<L\), the
decrements in two consecutive rows satisfy

\[
 \begin{aligned}
 |x_k|\{(1-|a_k|)+b_k(1-|c_k|)
 &+b_k\operatorname{dist}(\gamma_k,2\pi\mathbb Z)^2\}\\
 &\le C_Z(\Delta_k+\Delta_{k+1}),
 \end{aligned}
 \tag{A.50}
\]

*Proof.* For \(A,B\ge0\),

\[
 A+B-|Ae^{\mathrm iu}+Be^{\mathrm iv}|
 \ge\frac{2AB}{\pi^2(A+B)}
       \operatorname{dist}(u-v,2\pi\mathbb Z)^2.
 \tag{A.51}
\]

Put \(S=q_kx_k+y_k\) and \(X=|x_k|\).  If
\(|S|<q_kX/2\), then \(D_k\ge q_kX/2\ge\underline q_Z X/2\), which controls every term
on the left of (A.50).  Otherwise the two radial terms in (A.49) control the
first two terms of (A.50).  If either \(|a_k|<1/2\) or \(|c_k|<1/2\), a
radial term also controls the phase term. We may therefore assume
\(|a_k|,|c_k|\ge1/2\).  Then

\[
 |x_{k+1}|\ge\underline q_Z X/4,
 \qquad |y_{k+1}|\ge b_kX/2.
\]

Let \(\alpha\) be the circular angle from \(x_k\) to \(S\).  A direct
rationalization gives the required cost as follows.  Put
\(A=q_kX\), \(R=|S|\), and \(Y=|y_k|\). If \(Y=0\) and \(R=A\), then
\(S=q_kx_k\), so \(\alpha=0\), and the desired phase term vanishes. In every
other case with \(R\ge A\), the denominator below is positive and

\[
 D_k=A+Y-R
 =\frac{2AR(1-\cos\alpha)}{Y+R-A}
 \ge A(1-\cos\alpha),
\]

because \(Y+R-A\le2R\). If \(A/2<R<A\), then

\[
 D_k\ge Y-(A-R)
 =\frac{2AR(1-\cos\alpha)}{Y+A-R}
 \ge R(1-\cos\alpha).
\]

If \(R\le A/2\), then \(D_k\ge A-R\ge A/2\).  Since
\(1-\cos t\ge2\operatorname{dist}(t,2\pi\mathbb Z)^2/\pi^2\), these three
cases give

\[
 D_k\ge c_ZX\operatorname{dist}(\alpha,2\pi\mathbb Z)^2.
\]

Applying (A.51) at the next row gives

\[
 D_{k+1}\ge c_Zb_kX
 \operatorname{dist}(\beta,2\pi\mathbb Z)^2,
\]

where \(\beta\) is the circular angle from \(x_{k+1}\) to \(y_{k+1}\).
Indeed,
\(q_{k+1}|x_{k+1}|\ge\underline q_Z^2X/4\) and
\(b_kX/2\le|y_{k+1}|\le b_kX\), so the harmonic coefficient in
(A.51) is at least a \(Z\)-dependent multiple of \(b_kX\).
The row identities

\[
 x_{k+1}=a_kS,\qquad
 y_{k+1}=b_ke^{\mathrm i\theta}c_kx_k
\]

show explicitly that

\[
 \begin{aligned}
 \beta
 &=\arg y_{k+1}-\arg x_{k+1}\\
 &=\bigl(\theta+\arg c_k-\arg a_k\bigr)
   -\bigl(\arg S-\arg x_k\bigr)
 =\gamma_k-\alpha\pmod{2\pi}.
 \end{aligned}
\]

The circular triangle inequality, followed by
\((a+b)^2\le2a^2+2b^2\), proves (A.50).  All zero-vector cases were already
covered by the radial terms. \(\square\)

**Sublemma A.8.3 (summation of relative decrements).** If \(N_k>0\) for every
\(k\le L\), then the relative decrements control the total path occupation
weight through (A.55).

*Proof.* The root probability \(\bar b\) in (A.48) is formed without the distinguished
child, whereas \(b_k\) includes it.  Their odds differ by the distinguished
child vacancy \(q_{k+1}\in[\underline q_Z,1]\), and therefore

\[
 \underline q_Z\bar b\le b_k\le\bar b.
\]

Thus (A.48) and (A.50) imply

\[
 b_kh|x_k|\le C_Z(\Delta_k+\Delta_{k+1}),
 \qquad k<L-1.
 \tag{A.52}
\]

To remove the factor \(|x_k|\), put

\[
 Q_k=\prod_{U\in\operatorname{Comp}(\mathcal S_k)}(1-b_U).
\]

The recursion for the positive occupation probabilities gives

\[
 b_{k+1}\le z,\qquad b_k\ge\underline q_Z^2zQ_k.
 \tag{A.53}
\]

If \(Q_k\ge1/2\), then \(b_{k+1}\le C_Zb_k\).  If \(Q_k<1/2\), then
\(\sum_{U\in\operatorname{Comp}(\mathcal S_k)}b_U>1/2\), and (A.46) together with
Lemma A.4, applied componentwise, gives

\[
 1-|a_k|\ge c_Zh.
 \tag{A.54}
\]

Assume first that every \(N_k>0\), and set

\[
 \delta_k=\frac{N_k-N_{k+1}}{N_k}.
\]

If \(|x_k|\ge N_k/2\), (A.52) controls \(b_kh\) through
\(C_Z(\delta_k+\delta_{k+1})\).  If \(|x_k|<N_k/2\), then \(k\ge1\) and

\[
 |y_k|=b_{k-1}|c_{k-1}||x_{k-1}|>N_k/2.
\]

If \(N_{k-1}>2N_k\), the single decrement \(\delta_{k-1}>1/2\) gives the
bounded quantity \(b_kh\).  Otherwise
\(|x_{k-1}|\ge N_{k-1}/4\).  Apply (A.53)--(A.54) at \(k-1\): if
\(Q_{k-1}\ge1/2\), (A.53) gives
\(b_k\le2\underline q_Z^{-2}b_{k-1}\), and (A.52) at \(k-1\) gives

\[
 b_kh\le C_Z(\delta_{k-1}+\delta_k).
\]

Suppose instead that \(Q_{k-1}<1/2\), and put
\(S_{k-1}=q_{k-1}x_{k-1}+y_{k-1}\).  By (A.54),
\(1-|a_{k-1}|\ge c_Zh\).  If
\(|S_{k-1}|\ge\underline q_Z N_{k-1}/8\), the radial decrement in (A.49) gives

\[
 \Delta_{k-1}\ge(1-|a_{k-1}|)|S_{k-1}|
 \ge c_ZhN_{k-1}.
\]

If \(|S_{k-1}|<\underline q_Z N_{k-1}/8\), then

\[
 D_{k-1}\ge q_{k-1}|x_{k-1}|-|S_{k-1}|
 \ge\underline q_Z N_{k-1}/8.
\]

Thus \(\delta_{k-1}\ge c_Zh\) in either subcase, and this controls \(b_kh\)
because \(b_k\le1\). The four cases above use the following relative
decrements:

\[
 \begin{array}{c|c}
 \text{case at row }k&\text{controlling relative decrements}\\ \hline
 |x_k|\ge N_k/2&\delta_k+\delta_{k+1}\\
 |x_k|<N_k/2,\ N_{k-1}>2N_k&\delta_{k-1}\\
 Q_{k-1}\ge1/2&\delta_{k-1}+\delta_k\\
 Q_{k-1}<1/2&\delta_{k-1}
 \end{array}
\]

A fixed \(\delta_j\) can therefore occur only in the estimates for rows
\(j-1,j,j+1\), so it is counted at most three times. The final unpaired row
contributes at most one. Finally,

\[
 \sum_{k<L}\delta_k
 \le\sum_{k<L}-\log\frac{N_{k+1}}{N_k}
 =\log\frac1{N_L},
\]

because \(1-t\le-\log t\).  Summation gives

\[
 h\sum_{k<L}b_k\le C_Z\left(1+\log\frac1{N_L}\right).
 \tag{A.55}
\]

\(\square\)

If some \(N_k=0\), every later norm vanishes and the desired estimate is
immediate. Otherwise Sublemma A.8.3 yields

\[
 N_L\le C_Z\exp\left\{-c_Zh\sum_{k<L}b_k\right\}.
 \tag{A.56}
\]

It remains to include the side barriers \(\Lambda_k\). For every component
\(U\) of \(\mathcal S_k\), the root calculation in (A.46), applied to \(U\)
at its own root, gives

\[
 V_{U,z}\ge\underline q_Z^2b_U,
 \qquad \min\{V_{U,z},1\}\ge\underline q_Z^2b_U.
\]

Lemma A.4 and additivity of logarithmic loss over the independent components
therefore give

\[
 -\log|a_k|\ge c_Zh
 \sum_{U\in\operatorname{Comp}(\mathcal S_k)}b_U
 \ge c_Zh\Lambda_k,
 \tag{A.57}
\]

where the last inequality uses
\(-\log(1-b_U)\le b_U/\underline q_Z\).  Put \(r_k=|a_k|\).  The full root odds are

\[
 \frac{b_k}{q_k}=zq_{k+1}e^{-\Lambda_k}.
\]

There is \(c_Z>0\) such that, uniformly for \(0\le h\le1\) and
\(\Lambda\ge0\),

\[
 r_kq_k+b_k\le e^{-c_Zh\Lambda_k}.
 \tag{A.58}
\]

For clarity, this scalar estimate requires no compactness theorem.  Let
\(a_Z>0\) be the constant in (A.57), and put \(t=h\Lambda\).  If
\(t\le1\), then (A.57) and \(q_k\ge\underline q_Z\) give

\[
 1-(r_kq_k+b_k)=q_k(1-r_k)
 \ge\underline q_Z(1-e^{-a_Zt})
 \ge\underline q_Z(1-e^{-a_Z})t.
\]

If \(t\ge1\), the same bound gives
\(r_kq_k+b_k\le1-\delta_Z\), where
\(\delta_Z=\underline q_Z(1-e^{-a_Z})>0\).  On the other hand,

\[
 r_kq_k+b_k\le e^{-a_Zt}+Ze^{-\Lambda}
 \le e^{-a_Zt}+Ze^{-t}.
\]

Let \(m_Z=\min\{a_Z,1\}\), and choose \(T_Z<\infty\) so that
\((1+Z)e^{-m_Zt}\le e^{-m_Zt/2}\) for \(t\ge T_Z\).  On
\([1,T_Z]\), \(1-\delta_Z\le e^{-c_Zt}\) after choosing
\(c_Z\le-T_Z^{-1}\log(1-\delta_Z)\); for \(t\ge T_Z\), use the last
display and choose \(c_Z\le m_Z/2\).  Together with the \(t\le1\) estimate,
this proves (A.58) with uniform constants.

Finally, (A.49) also gives

\[
 N_{k+1}\le(r_kq_k+b_k)N_k.
\]

Multiplying and using (A.58) yields exponential decay in
\(h\sum_k\Lambda_k\).  Taking the geometric mean with (A.56) gives

\[
 N_L\le C_Z\exp\left\{-c_Zh
                   \sum_{k<L}(b_k+\Lambda_k)\right\}.
\]

The pairing with \(f_L\) is at most \(N_L\), which proves (A.43).  \(\square\)

## A.6. Recursive decomposition along a maximal-modulus branch

Fix \(z\in(0,Z]\), \(|\theta|\le\pi\), and an ambient finite rooted tree.
For a nonempty descendant subtree \(U=T_v\), define its scale and logarithmic
Fourier loss by

\[
 x_U=\theta^2V_{U,z},\qquad \ell_U=\ell_{U,z}(\theta).
\]

The two deletion forests associated with \(U\) are
\(Q_U=U-v\) and \(R_U=U-N_U[v]\), at the same \(z\) and \(\theta\). Every
nonempty component of either forest is a strict descendant subtree.
When the current subtree is denoted by \(T\) and its root by \(r\), write
\(Q=T-r\) and \(R=T-N[r]\). Choose \(H\in\{Q,R\}\) so that

\[
 M_H(\theta)=\max\{M_Q(\theta),M_R(\theta)\}.
\]

Ties may be resolved arbitrarily.

The normalized root decomposition and the triangle inequality give

\[
 M_T\le qM_Q+bM_R\le M_H,
 \qquad
 \ell_T\ge\ell_H
 =\sum_{U\text{ component of }H}\ell_U.
 \tag{A.59}
\]

Fix a threshold

\[
 X_*>4A_Z\pi^2.
\]

For a subtree \(T\) with \(x_T\ge X_*\), call its root
**narrow** if \(H=R\) and

\[
 x_R<\frac{x_Q}{2A_Z}.
 \tag{A.60}
\]

If the root is not narrow, (A.29) implies

\[
 x_H\ge\delta_Zx_T,
 \qquad \delta_Z=(4A_Z^2)^{-1}.
 \tag{A.61}
\]

Indeed, \(x_T\le A_Zx_Q+2\pi^2\) gives
\(x_Q\ge x_T/(2A_Z)\); this handles \(H=Q\), and (A.60) handles the
nonnarrow \(H=R\) case.

Starting at a nonnarrow subtree, choose one component of \(H\) as the next
subtree and place all other components in a discarded family \(\mathcal D\).
A \(Q\)-choice moves one edge down the rooted tree.  An \(R\)-choice moves
two edges through the child containing the selected grandchild component.
Include that intermediate child in the path. After any finite number of
choices, the resulting decomposition consists of the nested selected subtrees,
the discarded components, and this vertex path. Let \(B\) be the final
subtree, and define

\[
 \mathcal K=\theta^2\left\{
 \sum_{v\text{ on the path above }B}b_v
 +\sum_{R\text{-choices at }v}
       \log\frac{I_{Q_v}(z)}{I_{R_v}(z)}\right\}.
 \tag{A.62}
\]

Here \(Q_v=T_v-v\) and \(R_v=T_v-N[v]\) are the two deletion forests of the
current descendant subtree \(T_v\).

**Lemma A.9 (maximal-modulus path decomposition).** The path, final subtree \(B\), and
discarded family \(\mathcal D\) above satisfy, simultaneously,

\[
 x_T\le C_Z\left(\mathcal K+x_B+
                    \sum_{U\in\mathcal D}x_U\right),
 \tag{A.63}
\]

\[
 \ell_T\ge\ell_B+\sum_{U\in\mathcal D}\ell_U,
 \tag{A.64}
\]

and

\[
 \ell_T\ge c_Z\mathcal K-C_Z.
 \tag{A.65}
\]

All members of \(\mathcal D\), together with \(B\), are pairwise disjoint
descendant subtrees.

**Proof.**  Apply Lemma A.7 to the filled path.  At a \(Q\)-choice, every
side subtree is a discarded component.  At an \(R\)-choice through
\(v-u-w\), each side child subtree \(T_s\), \(s\ne u\), obeys (A.29):

\[
 V_{T_s}\le A_Z\sum_{t\in\operatorname{ch}(s)}V_{T_t}+2b_s.
\]

The \(T_t\)'s on the right, and the side children of \(u\) other than \(w\),
are discarded \(R\)-components.  Also

\[
 \sum_{s\in\operatorname{ch}(v)}b_s
 \le\sum_s-\log(1-b_s)
 =\log\frac{I_{Q_v}(z)}{I_{R_v}(z)}.
\]

No descendant subtree is used at two different choices. Multiplying (A.40) by
\(\theta^2\) proves (A.63).

At every choice, (A.59) gives the loss of the distinguished component plus
all newly discarded components.  Repeated substitution, rather than addition
of inequalities containing repeated intermediate losses, proves (A.64).

For (A.65), apply Lemma A.8 to the filled path.  At an \(R\)-choice through
\(v-u-w\),

\[
 \log\frac{I_{Q_v}(z)}{I_{R_v}(z)}
 =\sum_{s\ne u}-\log(1-b_s)-\log(1-b_u).
\]

The first sum is the side barrier \(\Lambda_v\), while
\(-\log(1-b_u)\le b_u/\underline q_Z\) is bounded by the contribution of the next path vertex \(u\), which
lies above \(B\).  Finally,
\(\sin^2(\theta/2)\ge\theta^2/\pi^2\).  Taking logarithms in (A.43) proves
(A.65).  Disjointness follows because all later discarded subtrees lie
inside the preceding distinguished subtree, whereas earlier discarded
subtrees lie outside it.  \(\square\)

A high-scale narrow subtree already has a direct loss estimate. Indeed, summing (A.29) over its child
subtrees and using (A.60) gives

\[
 \log\frac{I_Q(z)}{I_R(z)}\ge\sum_sb_s>\frac{V_Q}{4}.
\]

We record directly the scalar one-row estimate needed here.  Write

\[
 \Lambda=\log\frac{I_Q(z)}{I_R(z)},\qquad
 a=\frac{I_Q(ze^{\mathrm i\theta})}{I_Q(z)},\qquad
 c=\frac{I_R(ze^{\mathrm i\theta})}{I_R(z)}.
\]

The root decomposition and the triangle inequality give

\[
 M_T(\theta)=|qa+be^{\mathrm i\theta}c|\le q|a|+b.
\]

Moreover \(b/q=ze^{-\Lambda}\), while (A.57) gives
\(|a|\le\exp(-a_Zh\Lambda)\).  The scalar argument used in the proof of
(A.58), with no distinguished-child factor, therefore yields

\[
 M_T(\theta)\le\exp(-c_Zh\Lambda).
\]

For a narrow subtree, (A.30) and (A.60) imply

\[
 V_Q\le A_ZV_R+2\Lambda<\frac{V_Q}{2}+2\Lambda,
 \qquad \Lambda>\frac{V_Q}{4}.
\]

The high-scale estimate immediately preceding (A.61) also gives
\(x_Q\ge x_T/(2A_Z)\).  Since \(h\ge\theta^2/\pi^2\), we conclude that

\[
 \ell_T\ge c_Zh\Lambda\ge c_Z\theta^2V_Q\ge c_Zx_T.
\]

After decreasing \(c_Z\), this proves the stated, slightly weaker form

\[
 \ell_T\ge c_Zx_T-C_Z
 \tag{A.66}
\]

for every high-scale narrow subtree.

We now complete the proof of Theorem A.1. Let

\[
 H_\alpha(x)=\min\{x,x^\alpha\},\qquad 0<\alpha<1.
\]

This function is increasing and concave on \([0,\infty)\), with
\(H_\alpha(0)=0\).

Let \(C_1\ge1\) dominate both the constant in (A.63) and that constant
multiplied by \(\delta_Z^{-1}\). Choose

\[
 0<\sigma<\frac1{16C_1},\qquad a_0=\frac1{2C_1}.
\]

Choose a bounded-scale threshold \(X_0\ge X_*\), to be enlarged below, and
fix a descendant subtree \(T\) of scale \(X=x_T\ge X_0/\sigma\). We define one
finite path decomposition and its recursive family only after removing the
direct narrow case. If \(T\) is narrow, (A.66) applies and no recursive family
is formed. Suppose henceforth that \(T\) is not narrow. At the current
subtree \(U\):

1. stop if \(x_U\le X_0\) or if \(U\) is narrow;
2. otherwise choose its deletion forest \(H_U\) by the preceding
   maximal-modulus rule; if exactly one
   component \(W\) of \(H_U\) satisfies \(x_W>\sigma X\), put every other
   component of \(H_U\) into the discarded family and continue with \(W\);
3. stop if no component or at least two components of \(H_U\) have scale
   greater than \(\sigma X\).

Continue until the rule stops, let \(B\) be the final subtree, and let
\(\mathcal D\) be the union of all discarded component families. Define the
recursive family
\(\mathcal C(T)\) by

\[
 \mathcal C(T)=
 \begin{cases}
  \mathcal D\cup\{B\},&x_B\le X_0\text{ or }B\text{ is narrow},\\
  \mathcal D\cup\operatorname{Comp}(H_B),&\text{otherwise}.
 \end{cases}
\]

**Lemma A.10 (recursive-decomposition bookkeeping).** For every nonnarrow
descendant subtree \(T\) to which the preceding construction is applied, the
continuation terminates. The family \(\mathcal C(T)\) consists of pairwise
disjoint strict descendant subtrees, no intermediate logarithmic loss is
counted more than once, and

\[
 \ell_T\ge\sum_{U\in\mathcal C(T)}\ell_U.
\]

Moreover, the constant \(C_1=C_1(Z)\) chosen above satisfies (A.67).

*Proof.* Every continuation replaces the current subtree by a strict
descendant subtree, so finiteness of \(T\) proves termination.

In the second case the stopping rule says that the final deletion forest has either
no component above \(\sigma X\) or at least two such components. Every member
of \(\mathcal D\) was discarded at a step having a unique component above
\(\sigma X\), and hence has scale at most \(\sigma X\). The members of
\(\mathcal C(T)\) are pairwise disjoint strict descendant subtrees: discarded
subtrees at an earlier step lie outside every later selected subtree, and the
components of the final deletion forest are disjoint inside \(B\). If \(B\)
itself is included, then the selected path has positive length: the initial subtree
was neither bounded-scale nor narrow, whereas retaining \(B\) means that a later subtree is
bounded-scale or narrow.

After \(t\) continuation steps, let \(B_t\) be the distinguished component
still being followed and let \(\mathcal D_{\le t}\) be all components discarded
so far. Induction in (A.64) gives the invariant

\[
 \ell_T\ge \ell_{B_t}+\sum_{U\in\mathcal D_{\le t}}\ell_U,
\]

and the members of \(\mathcal D_{\le t}\), together with \(B_t\), are pairwise
disjoint. At the next step, (A.64) replaces the single term \(\ell_{B_t}\) by
the loss of the new distinguished component plus the newly discarded
components. Hence no earlier loss remains to be counted again. At termination,
(A.59) is used only if the final distinguished component is replaced by its
deletion-forest components. This proves the exact loss comparison

\[
 \ell_T\ge\sum_{U\in\mathcal C(T)}\ell_U.
\]

Likewise, (A.63) gives the required scale comparison when \(B\) is retained. When
\(B\) is replaced by the components of its deletion forest, (A.61) gives
\(x_B\le\delta_Z^{-1}x_{H_B}\), and forest variance additivity gives
\(x_{H_B}=\sum_{U\in\operatorname{Comp}(H_B)}x_U\). Thus the chosen
\(C_1=C_1(Z)\) satisfies in both cases

\[
 X\le C_1\left(\mathcal K+
              \sum_{U\in\mathcal C(T)}x_U\right).
 \tag{A.67}
\]

\(\square\)

Except for a narrow endpoint with \(x_B\ge\sigma X\), which is treated
directly below, the stopping rule gives the following dichotomy for the child
scales:

\[
 \begin{split}
 &x_i\le\sigma X\quad\text{for every }i,\quad\text{or}\\
 &\text{at least two of the }x_i\text{ exceed }\sigma X.
 \end{split}
 \tag{A.68}
\]

Indeed, a retained bounded bottom has \(x_B\le X_0\le\sigma X\), and a
retained narrow bottom that is not covered by the direct estimate below has
\(x_B<\sigma X\).

There are two direct cases. If \(\mathcal K\ge X/(2C_1)\), (A.65) gives
\(\ell_T\ge c_ZX-C_Z\). If a narrow bottom has
\(x_B\ge\sigma X\), then (A.64) and (A.66) give the same form of estimate,
with another constant depending only on \(Z\) and \(\sigma\). After increasing
the fixed scale threshold, either estimate implies
\(\ell_T\ge c_ZH_\alpha(X)\). No estimate on the descendants is used in these
two cases.

In every other case, (A.67) gives

\[
 \sum_i x_i\ge a_0X.
 \tag{A.69}
\]

Choose \(\alpha=\alpha_Z\in(0,1)\) sufficiently small that, for some fixed
\(\zeta>0\),

\[
 2\sigma^\alpha>1+\zeta,
 \qquad \frac{a_0}{\sigma}\sigma^\alpha>1+\zeta.
\]

This is possible because \(a_0/\sigma>8\) and
\(\sigma^\alpha\to1\) as \(\alpha\downarrow0\).  If at least two children
exceed \(\sigma X\), monotonicity gives

\[
 \sum_iH_\alpha(x_i)\ge2H_\alpha(\sigma X)
 =2\sigma^\alpha H_\alpha(X)
 >(1+\zeta)H_\alpha(X)
\]

once \(\sigma X\ge1\).  If all children are at most \(\sigma X\), concavity
and \(H_\alpha(0)=0\) give the chord bound

\[
 H_\alpha(t)\ge\frac{t}{\sigma X}H_\alpha(\sigma X),
 \qquad 0\le t\le\sigma X.
\]

Using (A.69),

\[
 \sum_iH_\alpha(x_i)
 \ge\frac{a_0}{\sigma}H_\alpha(\sigma X)
 >(1+\zeta)H_\alpha(X).
 \tag{A.70}
\]

Thus every case not covered by a direct estimate satisfies a strict
\(H_\alpha\)-gain.

We finish by strong induction on the number of vertices. The induction claim
is that, simultaneously for every rooted tree \(U\), every \(0<z\le Z\), and
every \(|\theta|\le\pi\),

\[
 \ell_U\ge c_ZH_{\alpha_Z}(x_U),
\]

with constants depending only on \(Z\). Choose the global scale threshold
large enough to absorb the additive constants in (A.65)--(A.66), to ensure
\(\sigma X\ge1\) in the high-scale argument, and to contain \(X_0/\sigma\).
Equation (A.39), with this fixed bounded range, proves the induction claim
below the threshold. The two direct cases above prove it at high scale without
an induction hypothesis. In every remaining case, all members of
\(\mathcal C(U)\) are pairwise disjoint strict descendant subtrees, so the strong
induction hypothesis applies to each. The exact loss comparison above and
(A.70) give

\[
 \ell_U\ge\sum_{W\in\mathcal C(U)}\ell_W
 \ge c_Z\sum_{W\in\mathcal C(U)}H_{\alpha_Z}(x_W)
 \ge c_ZH_{\alpha_Z}(x_U).
\]

Taking \(c_Z\) to be the minimum of the bounded-scale and direct-estimate constants
proves (A.3) for every finite tree.  The case \(\theta=0\) has both sides
equal to zero.

For a forest with tree components \(T_i\), variances and logarithmic losses
add.  Concavity and \(H_\alpha(0)=0\) imply subadditivity:

\[
 H_\alpha\!\left(\sum_i x_i\right)\le\sum_iH_\alpha(x_i).
\]

Indeed, for \(a,b\ge0\), concavity gives
\(H_\alpha(a)\ge aH_\alpha(a+b)/(a+b)\) and
\(H_\alpha(b)\ge bH_\alpha(a+b)/(a+b)\); finite iteration proves the
displayed inequality.

Hence the same estimate holds for every finite forest, completing the proof
of (A.3).  Finally,

\[
 \inf_{x\ge0}\frac{H_{\alpha_Z}(x)}{\log(1+x)}>0,
\]

with the ratio at \(x=0\) interpreted by continuity.  This proves (A.4) and
Theorem A.1.  \(\square\)

## A.7. Aggregate tail consequence

For Corollary A.2, let \(F_n\) be the disjoint union of the forests
\(F_{n,j}\). Its hard-core count is the sum of the independent counts in the
corollary, its variance is \(W_n\), and its centered characteristic function
is \(\Phi_n\). Theorem A.1 therefore gives, for
\(|u|\le\pi\sqrt{W_n}\),

\[
 \left|\Phi_n\!\left(\frac{u}{\sqrt{W_n}}\right)\right|
 \le \exp\{-c_Z\min(u^2,|u|^{2\alpha_Z})\}.
\]

The right-hand side is integrable against \(1+u^2\). Its integral over
\(|u|\ge R\) tends to zero as \(R\to\infty\), uniformly in \(n\), which is
(A.5). \(\square\)



The proof above is self-contained for the hard-core model on finite forests.
Its only general-purpose inputs are finite conditional expectation and total
variance, Cauchy--Schwarz, Markov's inequality, the finite Doob maximal
inequality proved in Lemma A.3, elementary trigonometric and concavity
inequalities, and finite matrix multiplication.  In particular, the
small-frequency curvature estimate, the uniform characteristic-function gap, and
the bounded-scale compactness lemma are all proved here with their full
uniform quantifiers. No additional specialized theorem is invoked without a
proof in this appendix.

# Appendix B. Compact limits and low-activity Gaussianity

This appendix proves the two analytic theorems used in Appendix C.  Section B.1
establishes the canonical compact-limit and local-curvature formula.  Section
B.2 proves a central limit theorem at activity at most \(3/2\), with constants
independent of the order, component count, degrees, depths, and topology of
the forest.

## B.1. Canonical compact limits and curvature inversion

For a finite forest \(F\), write

\[
 I_F(t)=\sum_{k=0}^{\alpha(F)}i_k(F)t^k,                 \tag{B.1}
\]

where \(i_k(F)\) is the number of independent \(k\)-subsets of \(V(F)\) and
\(\alpha(F)\) is the independence number.  At activity \(z>0\), the hard-core
law is

\[
 \Pr_z(I)=\frac{z^{|I|}}{I_F(z)},\qquad I\subseteq V(F)
 \text{ independent},                                  \tag{B.2}
\]

and \(X=|I|\) denotes the total number of occupied vertices.  If the coefficient
sequence falls and then rises, define

\[
 m=\min\{k:i_k>i_{k+1}\},\qquad
 s=\min\{k>m:i_k<i_{k+1}\}.
\]

The integer \(s\) is the first-recovery index. Its minimality gives

\[
 i_{s-1}\ge i_s<i_{s+1},\qquad i_s^2<i_{s-1}i_{s+1}.
                                                               \tag{B.3}
\]

The canonical activity is the unique \(z>0\) for which
\(\mathbb E_zX=s\), and the canonical variance is
\(V=\operatorname{Var}_zX\).  Existence and uniqueness follow from

\[
 \frac{d}{d\log z}\mathbb E_zX=\operatorname{Var}_zX>0
\]

and from the limits of \(\mathbb E_zX\) as \(z\) tends to zero and infinity.
Thus a canonical first-recovery sequence
\((F_n,s_n,z_n,V_n)\) comes with integer-valued random variables \(X_n\)
satisfying

\[
 \mathbb E X_n=s_n,\qquad \operatorname{Var}X_n=V_n.    \tag{B.4}
\]

For \(j\in\mathbb Z\), set

\[
 p_n(j)=\Pr(X_n=s_n+j),\qquad
 \Delta_n=p_n(0)^2-p_n(-1)p_n(1).                      \tag{B.5}
\]

The activity factors in (B.2) cancel from the adjacent log-concavity
difference:

\[
 \Delta_n=\frac{z_n^{2s_n}}{I_{F_n}(z_n)^2}
 \left(i_{s_n}(F_n)^2-i_{s_n-1}(F_n)i_{s_n+1}(F_n)\right)<0.
\]

We use one result from Appendix A and no other Fourier-decay input.  Theorem
A.1, specialized to the
activity ceiling \(27\), supplies constants \(c_{27}>0\) and
\(\alpha_{27}\in(0,1)\) such that, for every finite forest at activity
\(0<z<27\),

\[
 \left|\mathbb E_z e^{\mathrm i\theta(X-\mathbb E_zX)}\right|
 \le
 \exp\!\left\{-c_{27}\min\left(
       V\theta^2,(V\theta^2)^{\alpha_{27}}\right)\right\},
 \qquad |\theta|\le\pi.                               \tag{B.6}
\]

This full fundamental-domain estimate, rather than a compact-frequency
version of it, is essential below.

**Theorem B.1 (canonical local-limit curvature theorem).**  Let
\((F_n,s_n,z_n,V_n)\) be a canonical first-recovery sequence such that
\(0<z_n<27\) and \(V_n\to\infty\).  From every subsequence one can extract a
further subsequence, indexed again by \(n\), for which

\[
 Y_n:=\frac{X_n-s_n}{\sqrt{V_n}}\Rightarrow Y           \tag{B.7}
\]

for a probability law having a \(C^2\) density \(f\).  If

\[
 \phi_n(u)=\mathbb E e^{\mathrm iuY_n},\qquad
 D_n=[-\pi\sqrt{V_n},\pi\sqrt{V_n}],\qquad
 \widetilde\phi_n=\mathbf 1_{D_n}\phi_n,              \tag{B.8}
\]

and \(\phi\) is the characteristic function of \(Y\), then, for
\(m\in\{0,1,2\}\),

\[
 \int_{\mathbb R}(1+|u|^m)
       |\widetilde\phi_n(u)-\phi(u)|\,du\longrightarrow0.   \tag{B.9}
\]

Moreover,

\[
 V_n^2\bigl[p_n(0)^2-p_n(-1)p_n(1)\bigr]
 \longrightarrow (f'(0))^2-f(0)f''(0).                \tag{B.10}
\]

When \(f(0)>0\), the expression on the right is
\(f(0)^2[-(\log f)''(0)]\). This identity explains the use of the term
curvature in the theorem title; no separate notion of curvature is being
introduced.

In particular, every such limiting density satisfies
\((f'(0))^2-f(0)f''(0)\le0\).

**Proof.**  Begin with an arbitrary subsequence.  By (B.4),
\(\mathbb EY_n=0\) and \(\mathbb EY_n^2=1\).  Chebyshev's inequality makes
the laws of \(Y_n\) tight, so Prokhorov's theorem gives a further weakly
convergent subsequence.  Denote its limiting law by that of \(Y\).  The uniform
second-moment bound also makes \((Y_n)\) uniformly integrable in \(L^1\), so
\(\mathbb EY=0\); lower semicontinuity gives
\(\mathbb EY^2\le1\).  No equality of limiting variances is needed.

Define

\[
 H_{27}(u)=\exp\!\left\{-c_{27}\min
       (u^2,|u|^{2\alpha_{27}})\right\}.               \tag{B.11}
\]

Substitution of \(\theta=u/\sqrt{V_n}\) into (B.6), using the exact centering
in (B.4), gives

\[
 |\phi_n(u)|\le H_{27}(u),\qquad u\in D_n.             \tag{B.12}
\]

The weights \(1\), \(|u|\), and \(|u|^2\) are integrable against \(H_{27}\).
Weak convergence
and the Lévy continuity theorem give \(\phi_n(u)\to\phi(u)\) for each fixed
\(u\).  Since the intervals \(D_n\) exhaust \(\mathbb R\), (B.12) also gives
\(|\phi(u)|\le H_{27}(u)\).  Therefore

\[
 (1+|u|^m)|\widetilde\phi_n(u)-\phi(u)|
 \le2(1+|u|^m)H_{27}(u),                              \tag{B.13}
\]

and dominated convergence proves (B.9).

In particular, \(|u|^m\phi(u)\in L^1(\mathbb R)\) for \(m=0,1,2\).
Fourier inversion identifies the limiting law with the density

\[
 f(x)=\frac1{2\pi}\int_{\mathbb R}e^{-\mathrm iux}\phi(u)\,du,\qquad
 f^{(m)}(x)=\frac1{2\pi}\int_{\mathbb R}
      (-\mathrm iu)^m e^{-\mathrm iux}\phi(u)\,du.     \tag{B.14}
\]

Thus \(f\in C^2(\mathbb R)\).

It remains to prove the local statement.  Because \(s_n\) is an integer,
lattice Fourier inversion on the scaled fundamental domain gives, for every
\(j\in\mathbb Z\),

\[
 p_n(j)=\frac1{2\pi\sqrt{V_n}}
 \int_{D_n}e^{-\mathrm iuj/\sqrt{V_n}}\phi_n(u)\,du.
                                                               \tag{B.15}
\]

Applying (B.15) to \(j=-1,0,1\), taking the real part, and using the zero
extension in (B.8) yields the exact identity

\[
 V_n^2\Delta_n
 =\frac1{(2\pi)^2}\operatorname{Re}
 \iint_{\mathbb R^2}K_{V_n}(u,v)
       \widetilde\phi_n(u)\widetilde\phi_n(v)\,du\,dv, \tag{B.16}
\]

where

\[
 K_V(u,v)=V\left(1-\cos\frac{u-v}{\sqrt V}\right).
                                                               \tag{B.17}
\]

Indeed, the imaginary sine part of
\(V_n[1-e^{\mathrm i(u-v)/\sqrt{V_n}}]\) integrates to zero exactly:
\(\phi_n(u)\phi_n(v)\) and \(D_n\times D_n\) are invariant under interchanging
\(u\) and \(v\), whereas \(\sin((u-v)/\sqrt{V_n})\) is antisymmetric.

There is no complex conjugate in (B.16): the product
\(p_n(-1)p_n(1)\) produces the phase
\(e^{\mathrm i(u-v)/\sqrt{V_n}}\).  For all \(u,v\),

\[
 0\le K_{V_n}(u,v)\le\frac{(u-v)^2}{2},\qquad
 K_{V_n}(u,v)\longrightarrow\frac{(u-v)^2}{2}.         \tag{B.18}
\]

The absolute value of the integrand in (B.16) is consequently bounded by

\[
 \frac{(u-v)^2}{2}H_{27}(u)H_{27}(v),                 \tag{B.19}
\]

which is integrable on \(\mathbb R^2\).  Dominated convergence, equivalently
the weighted convergence (B.9) with \(m=2\), gives

\[
 \lim_{n\to\infty}V_n^2\Delta_n
 =\frac1{(2\pi)^2}\operatorname{Re}
   \iint_{\mathbb R^2}\frac{(u-v)^2}{2}
          \phi(u)\phi(v)\,du\,dv.                    \tag{B.20}
\]

From (B.14),

\[
 f'(0)=\frac1{2\pi}\int_{\mathbb R}(-\mathrm iu)\phi(u)\,du,
 \qquad
 f''(0)=\frac1{2\pi}\int_{\mathbb R}(-u^2)\phi(u)\,du. \tag{B.21}
\]

Expanding \((u-v)^2/2\) in (B.20) and symmetrizing shows that its right-hand
side is exactly \((f'(0))^2-f(0)f''(0)\).  This proves (B.10).  Finally,
\(\Delta_n<0\) for every \(n\), so the limiting curvature is nonpositive.
\(\square\)

The centering in Theorem B.1 is exact: the canonical activity is chosen so
that the integer \(s_n\) equals \(\mathbb EX_n\).  More generally, if an
integer center \(k_n\) is used and
\((X_n-k_n)/\sqrt{V_n}\) is tight, then

\[
 m_n=\frac{\mathbb EX_n-k_n}{\sqrt{V_n}}               \tag{B.22}
\]

is bounded.  Indeed, for \(R<|m_n|\), Chebyshev's inequality gives

\[
 \Pr\!\left(\left|\frac{X_n-k_n}{\sqrt{V_n}}\right|\le R\right)
 \le (|m_n|-R)^{-2}.                                  \tag{B.23}
\]

After extraction \(m_n\to m\), and Slutsky's theorem translates any weak
limit centered at the exact mean by \(m\).  In the canonical normalization
above, \(m_n=0\) identically.

## B.2. A uniform central limit theorem at low activity

**Theorem B.2 (low-activity CLT).**  Let \(F_n\) be arbitrary finite forests,
let \(0<z_n\le3/2\), and let \(X_n\) be the total occupation count under the
hard-core law on \(F_n\) at activity \(z_n\).  If

\[
 V_n:=\operatorname{Var}X_n\longrightarrow\infty,
\]

then

\[
 \frac{X_n-\mathbb EX_n}{\sqrt{V_n}}\Rightarrow N(0,1). \tag{B.24}
\]

**Proof.** Fix a finite forest \(F\), root every component arbitrarily, and
give each component root a fictitious absent parent. Order the components
arbitrarily and, within each component, order every parent before its
children. We establish estimates for this rooted forest at a fixed activity
\(0<z\le3/2\). All constants below are absolute and independent of \(F\),
its number of components, and \(z\) in this range.

**Boundary-conditioned recursion and martingale representation.**
For a vertex \(u\), let \(T_u\) be its descendant subtree.  Write \(P_u\) for
the partition function of the unrestricted hard-core law on \(T_u\) when the
parent of \(u\) is absent, \(Q_u\) for the partition function with \(u\)
forced absent, and \(R_u\) for the partition function with \(u\) forced
occupied.  If \(c\) ranges over the children of \(u\), then

\[
 P_u=Q_u+R_u,\qquad Q_u=\prod_cP_c,
 \qquad R_u=z\prod_cQ_c.                              \tag{B.25}
\]

Set

\[
 p_u=\frac{R_u}{P_u},\qquad q_u=1-p_u=\frac{Q_u}{P_u},
 \qquad \ell_u=\frac{p_u}{q_u}.
\]

The exact rooted-tree recursion for the occupation odds is

\[
 \ell_u=z\prod_cq_c,\qquad 0<\ell_u\le z.           \tag{B.26}
\]

Let \(\mu_u^P,\mu_u^Q,\mu_u^R\) denote the expected occupation count in
\(T_u\) in the three states just defined, and put

\[
 \delta_u=\mu_u^R-\mu_u^Q.                            \tag{B.27}
\]

Since
\(\mu_u^Q=\sum_c\mu_c^P\),
\(\mu_u^R=1+\sum_c\mu_c^Q\), and
\(\mu_c^P=q_c\mu_c^Q+p_c\mu_c^R\), these conditional mean differences obey

\[
 \delta_u=1-\sum_cp_c\delta_c.                       \tag{B.28}
\]

Let \(\xi_u\) be the occupation indicator of \(u\). Define

\[
 a_u=\Pr(\text{the parent of }u\text{ is absent}),
 \qquad w_u=a_up_uq_u,                                \tag{B.29}
\]

with \(a_r=1\) at every component root. For every child \(c\) of \(u\),

\[
 a_c=\Pr(\xi_u=0)=1-a_up_u.                           \tag{B.30}
\]

Order the vertices so that every parent precedes its children, and let
\(\mathcal F_{u^-}\) denote the sigma-field generated by the occupation
variables revealed before \(u\). The forest Markov property, component
independence, and (B.25) give

\[
 \mathbb E(\xi_u\mid\mathcal F_{u^-})
   =p_u(1-\xi_{\operatorname{par}(u)}).
\]

Consequently

\[
 \eta_u=\xi_u-p_u(1-\xi_{\operatorname{par}(u)})       \tag{B.31}
\]

is a martingale difference and

\[
 \mathbb E(\eta_u^2\mid\mathcal F_{u^-})
 =p_uq_u(1-\xi_{\operatorname{par}(u)}),
 \qquad \mathbb E\eta_u^2=w_u.                       \tag{B.32}
\]

In \(\sum_u\delta_u\eta_u\), the coefficient of \(\xi_u\) is
\(\delta_u+\sum_cp_c\delta_c=1\) by (B.28).  The sum has mean zero, so its
constant term is \(-\mathbb EX\).  Orthogonality of martingale differences
therefore gives the exact identities

\[
 X-\mathbb EX=\sum_u\delta_u\eta_u,
 \qquad
 V:=\operatorname{Var}X=\sum_uw_u\delta_u^2.          \tag{B.33}
\]

**Weighted transfer contractions.**
We next prove two contraction estimates that are uniform over the forest. For a vector
\(x=(x_u)_{u\in F}\), define the upward transfer operator and weighted norms by

\[
 (\mathcal Tx)_u=\sum_{c\text{ child of }u}p_cx_c,
 \qquad
 \|x\|_{r,w}^r=\sum_uw_u|x_u|^r.                     \tag{B.34}
\]

For all children \(c\) of a fixed \(u\), (B.30) gives

\[
 w_c=A_up_cq_c,\qquad A_u:=1-a_up_u,
 \qquad \frac{w_u}{A_u}\le p_u,                      \tag{B.35}
\]

because \(a_uq_u\le1-a_up_u\).  Cauchy--Schwarz now gives

\[
 \left|\sum_cp_cx_c\right|^2
 \le\left(\sum_c\frac{p_c}{q_c}\right)
       \left(\sum_cp_cq_cx_c^2\right),               \tag{B.36}
\]

and hence

\[
 w_u|(\mathcal Tx)_u|^2
 \le K_2(u)\sum_cw_cx_c^2,
 \qquad K_2(u)=p_u\sum_c\ell_c.                      \tag{B.37}
\]

Put

\[
 Y_u=\sum_c\log(1+\ell_c).
\]

Since \(q_c=(1+\ell_c)^{-1}\), (B.26) implies

\[
 p_u=\frac{z}{z+e^{Y_u}}.                             \tag{B.38}
\]

The function \(r/\log(1+r)\) is increasing on \((0,\infty)\).  Since
\(\ell_c\le z\),

\[
 \sum_c\ell_c\le\frac{z}{\log(1+z)}Y_u.
\]

Together with \(Y_ue^{-Y_u}\le e^{-1}\), this gives

\[
 K_2(u)\le\frac{z^2}{e\log(1+z)}
 \le\frac{9}{4e\log(5/2)}<\frac{15}{16}.              \tag{B.39}
\]

The middle expression is increasing in \(z\).  The last strict inequality
follows, for example, from \(e>8/3\) and \(\log(5/2)>9/10\).  Summing (B.37)
over parents, each nonroot child is counted once, and therefore

\[
 \|\mathcal Tx\|_{2,w}^2\le\frac{15}{16}\|x\|_{2,w}^2.
                                                               \tag{B.40}
\]

For the cubic estimate, Hölder's inequality gives

\[
 \left|\sum_cp_cx_c\right|^3
 \le\left(\sum_cp_cq_c|x_c|^3\right)
       \left(\sum_c\frac{p_c}{\sqrt{q_c}}\right)^2.
                                                               \tag{B.41}
\]

Using (B.35),

\[
 w_u|(\mathcal Tx)_u|^3
 \le K_3(u)\sum_cw_c|x_c|^3,
\]

where

\[
 K_3(u)=p_u\left(\sum_c\frac{p_c}{\sqrt{q_c}}\right)^2
 =p_u\left(\sum_c\frac{\ell_c}{\sqrt{1+\ell_c}}\right)^2.
                                                               \tag{B.42}
\]

Writing \(y=\log(1+r)\), one has
\(r/\sqrt{1+r}=2\sinh(y/2)\), and
\(2\sinh(y/2)/y\) is increasing for \(y>0\).  Hence

\[
 \sum_c\frac{\ell_c}{\sqrt{1+\ell_c}}
 \le\frac{z}{\sqrt{1+z}\log(1+z)}Y_u.
\]

Equations (B.38) and \(Y_u^2e^{-Y_u}\le4e^{-2}\) yield

\[
 K_3(u)\le
 \frac{4z^3}{e^2(1+z)\log^2(1+z)}
 \le\frac{27}{5e^2\log^2(5/2)}<\frac{15}{16}.         \tag{B.43}
\]

The first expression is increasing in \(z\): its logarithmic derivative has
the sign of
\((3+2z)\log(1+z)-2z>0\).  The last inequality follows from
\(e\log(5/2)>12/5\), as in (B.39).  Summing over parents gives

\[
 \|\mathcal Tx\|_{3,w}^3\le\frac{15}{16}\|x\|_{3,w}^3.
                                                               \tag{B.44}
\]

**Moments of the conditional mean differences.**
The gap recursion (B.28) is

\[
 \mathbf1=(I+\mathcal T)\delta.                      \tag{B.45}
\]

Let

\[
 W=\sum_uw_u,\qquad S_3=\sum_uw_u|\delta_u|^3.
\]

The triangle inequality, (B.33), and (B.40) imply

\[
 W^{1/2}=\|\mathbf1\|_{2,w}
 \le\left(1+\frac{\sqrt{15}}4\right)\|\delta\|_{2,w}
 =\left(1+\frac{\sqrt{15}}4\right)V^{1/2}.
\]

Similarly, (B.44)--(B.45) give

\[
 S_3^{1/3}\le W^{1/3}+\left(\frac{15}{16}\right)^{1/3}S_3^{1/3}.
\]

Thus

\[
 W\le C_WV,\qquad S_3\le C_3V,                       \tag{B.46}
\]

where

\[
 C_W=\left(1+\frac{\sqrt{15}}4\right)^2,
 \qquad
 C_3=\frac{C_W}{\left(1-(15/16)^{1/3}\right)^3}.      \tag{B.47}
\]

Conditional on an absent parent, \(\eta_u\) is a centered Bernoulli
variable, and therefore

\[
 \mathbb E(|\eta_u|^3\mid\xi_{\operatorname{par}(u)}=0)
 =p_uq_u(p_u^2+q_u^2)\le p_uq_u.
\]

If the parent is occupied, \(\eta_u=0\).  Consequently

\[
 \sum_u\mathbb E|\delta_u\eta_u|^3
 \le\sum_uw_u|\delta_u|^3
 =S_3\le C_3V.                                       \tag{B.48}
\]

**Predictable quadratic variation.**
We now concentrate the predictable quadratic variation.  From (B.32), it is

\[
 \mathscr V_F=\sum_up_uq_u\delta_u^2
       (1-\xi_{\operatorname{par}(u)}),
 \qquad \mathbb E\mathscr V_F=V,                    \tag{B.49}
\]

where every component-root parent indicator is fixed at zero.  Set

\[
 h_u=p_uq_u\delta_u^2,
 \qquad A_x=\sum_{c\text{ child of }x}h_c.
\]

The component-root terms are deterministic, and reindexing all other parent
indicators gives

\[
 \mathscr V_F=\text{a deterministic constant}-\sum_xA_x\xi_x.
                                                               \tag{B.50}
\]

We need a variance bound for deterministic linear scores.  Given coefficients
\(d_u\), let \(Y_d=\sum_ud_u\xi_u\), and define \(\theta\) recursively by

\[
 \theta_u=d_u-\sum_cp_c\theta_c.
\]

The coefficient calculation used in (B.33) gives

\[
 Y_d-\mathbb EY_d=\sum_u\theta_u\eta_u,
 \qquad
 \operatorname{Var}Y_d=\sum_uw_u\theta_u^2.          \tag{B.51}
\]

In vector notation, \(\theta=(I+\mathcal T)^{-1}d\).  The operator
\(\mathcal T\) is the direct sum of the component transfer operators and is
nilpotent on a finite rooted forest. Thus (B.40) gives

\[
 \operatorname{Var}Y_d
 \le\frac1{(1-\sqrt{15}/4)^2}\sum_uw_ud_u^2.          \tag{B.52}
\]

Applying (B.52) to \(d_x=A_x\) and using (B.50),

\[
 \operatorname{Var}\mathscr V_F
 \le\frac1{(1-\sqrt{15}/4)^2}\sum_xw_xA_x^2.         \tag{B.53}
\]

For each \(x\), define

\[
 S_x=\sum_cp_cq_c,\qquad
 B_x=\sum_cp_cq_c|\delta_c|^3.
\]

Hölder interpolation gives

\[
 A_x\le S_x^{1/3}B_x^{2/3}.                          \tag{B.54}
\]

If \(t_x=\sum_cp_c\), then \(S_x\le t_x\), while (B.26) and
\(q_c\le e^{-p_c}\) imply

\[
 w_x\le p_x\le z\prod_cq_c\le ze^{-t_x}.
\]

Since \(\max_{t\ge0}e^{-t}t^{2/3}=(2/(3e))^{2/3}\),

\[
 w_xS_x^{2/3}\le
 \frac32\left(\frac{2}{3e}\right)^{2/3}=:C_{\mathrm B}. \tag{B.55}
\]

For each child \(c\) of \(x\),

\[
 a_c=1-a_xp_x\ge q_x
 =\frac1{1+\ell_x}\ge\frac1{1+z}\ge\frac25.
\]

Hence

\[
 B_x\le\frac52\sum_{c\text{ child of }x}
                 w_c|\delta_c|^3,
 \qquad
 \sum_xB_x\le\frac52S_3\le\frac52C_3V.             \tag{B.56}
\]

The child sets of distinct parents are disjoint.  Using (B.54)--(B.56) and
\(\sum_xB_x^{4/3}\le(\sum_xB_x)^{4/3}\), we obtain

\[
 \sum_xw_xA_x^2
 \le C_{\mathrm B}\sum_xB_x^{4/3}
 \le C_{\mathrm B}\left(\frac52C_3V\right)^{4/3}.   \tag{B.57}
\]

Equations (B.49), (B.53), and (B.57) show that an absolute constant \(C_Q\)
satisfies

\[
 \operatorname{Var}\mathscr V_F\le C_QV^{4/3},
 \qquad
 \mathbb E\left|\frac{\mathscr V_F}{V}-1\right|^2
 \le C_QV^{-2/3}.                                    \tag{B.58}
\]

**Martingale limit.**
Return now to the sequence \((F_n,z_n)\). In each row, concatenate the
componentwise parent-before-child orders and define

\[
 D_{n,u}=\frac{\delta_{n,u}\eta_{n,u}}{\sqrt{V_n}}.
\]

By (B.33), their row sum is
\((X_n-\mathbb EX_n)/\sqrt{V_n}\).  By (B.58), their predictable quadratic
variation satisfies

\[
 \sum_u\mathbb E(D_{n,u}^2\mid\mathcal F_{n,u^-})
 =\frac{\mathscr V_{F_n}}{V_n}\longrightarrow1
 \quad\text{in }L^2.                                 \tag{B.59}
\]

For every \(\varepsilon>0\), the conditional Lindeberg sum \(L_n(\varepsilon)\)
obeys

\[
\begin{aligned}
 L_n(\varepsilon)
 &:=\sum_u\mathbb E\!\left(
       D_{n,u}^2\mathbf1_{\{|D_{n,u}|>\varepsilon\}}
       \mid\mathcal F_{n,u^-}\right),\\
 \mathbb E L_n(\varepsilon)
 &\le\frac1\varepsilon\sum_u\mathbb E|D_{n,u}|^3
 \le\frac{C_3}{\varepsilon\sqrt{V_n}}
 \longrightarrow0.                                  \tag{B.60}
\end{aligned}
\]

Thus \(L_n(\varepsilon)\to0\) in probability. We use the following standard
constant-variance form of the martingale triangular-array central limit
theorem: if each row is a finite square-integrable martingale-difference
array, its predictable quadratic variation converges in probability to one,
and its conditional Lindeberg sums converge in probability to zero, then its
row sum converges weakly to \(N(0,1)\). This is [HH80, Corollary 3.1, p. 58,
with the subsequent remark on p. 59 that removes the cross-row nesting
condition (3.21) when the limiting variance is a nonrandom constant].
Equation (B.59) is exactly the predictable-variance hypothesis and (B.60) is
the conditional Lindeberg hypothesis. The theorem gives (B.24), completing
the proof. \(\square\)

## B.3. Classical inputs

The compactness, convergence, and Fourier steps use Prokhorov's theorem, the
Lévy continuity theorem, Slutsky's theorem, and Fourier inversion for
integrable characteristic functions and integer-valued laws; see [Bil99] and
[Fel71].
The precise constant-variance form of the martingale triangular-array central
limit theorem used after (B.59)--(B.60) is stated there and attributed to
[HH80, Corollary 3.1, p. 58, and the subsequent remark on p. 59].

# Appendix C. Occupation balance and the scale of first recovery

This appendix proves two quantitative inputs used after Theorem 4.1. The
first is a uniform occupation-probability bound at a vertex with a dominant
variance contribution. The second compares the size, mean, and variance of a
canonical first-recovery state. All
conditional laws below are taken at the activity of the original global
forest. In particular, no component, descendant subtree, or conditional
binomial law is assigned a first-recovery property.

## C.1. Canonical states and two analytic theorems

Let \(F\) be a finite forest of order \(N\), with independence polynomial

\[
 I_F(t)=\sum_{k=0}^{\alpha(F)}i_k(F)t^k,
\]

where \(i_k(F)\) is the number of independent \(k\)-subsets of \(V(F)\) and
\(\alpha(F)\) is the independence number. If the coefficient sequence falls
and then rises, put

\[
 m=\min\{k:i_k>i_{k+1}\},\qquad
 s=\min\{k>m:i_k<i_{k+1}\}.
\]

Thus

\[
 i_{s-1}\ge i_s<i_{s+1},\qquad i_s^2<i_{s-1}i_{s+1}.       \tag{C.1}
\]

For \(z>0\), the hard-core law on \(F\) is

\[
 \Pr_z(I)=\frac{z^{|I|}}{I_F(z)},\qquad I\subseteq V(F)
 \text{ independent}.
\]

Write \(X=|I|\), and let \(\xi_u=\mathbf 1_{\{u\in I\}}\) be the occupation
indicator of \(u\). Since

\[
 \frac{d}{d\log z}\mathbb E_zX=\operatorname{Var}_zX>0,
\]

there is a unique activity \(z\) for which \(\mathbb E_zX=s\). We write

\[
 V=\operatorname{Var}_zX,\qquad
 \pi(j)=\Pr_z(X=s+j).
\]

The quadruple \((F,s,z,V)\) is the **canonical first-recovery state**. By
(C.1), its central log-concavity difference satisfies

\[
 \mathcal D_s:=\pi(0)^2-\pi(-1)\pi(1)<0.             \tag{C.2}
\]

A **canonical first-recovery sequence** is any sequence of these states. As
in Section 1, it is called **variance-divergent** when \(V_n\to\infty\); activity
restrictions are always stated separately.

We use the following two theorems proved in Appendix B. Theorem B.1 says that
from every subsequence of a variance-divergent canonical sequence with
\(0<z_n<27\), one may extract a further subsequence for which
\((X_n-s_n)/\sqrt{V_n}\) converges in distribution to a law with a \(C^2\)
density \(f\), and

\[
 V_n^2\mathcal D_{s_n}
 \longrightarrow (f'(0))^2-f(0)f''(0).             \tag{C.3}
\]

Theorem B.2 says that for arbitrary finite forests and activities
\(0<z_n\le3/2\), if \(V_n\to\infty\), then

\[
 \frac{X_n-\mathbb E X_n}{\sqrt{V_n}}
 \Rightarrow N(0,1).                               \tag{C.4}
\]

Lemma C.1 depends on both proved theorems: Theorem B.2 identifies the only
possible low-activity limit, while Theorem B.1 transfers the strict
first-recovery log-concavity difference to its limiting curvature.

**Lemma C.1 (activity lower bound at large variance).** There is
\(V_{\rm act}<\infty\)
such that every canonical first-recovery state with \(0<z<27\) and
\(V\ge V_{\rm act}\) satisfies

\[
 z>\frac32.                                         \tag{C.5}
\]

**Proof.** Otherwise there would be a variance-divergent canonical sequence with
\(z_n\le3/2\). Since \(\mathbb E X_n=s_n\), (C.4) makes
\((X_n-s_n)/\sqrt{V_n}\) converge to the standard normal law. Apply (C.3)
on a further subsequence. Its limiting density is
\(\varphi(x)=(2\pi)^{-1/2}e^{-x^2/2}\), and hence

\[
 (\varphi'(0))^2-\varphi(0)\varphi''(0)
 =\varphi(0)^2=\frac1{2\pi}>0.
\]

This contradicts (C.2), because every term \(V_n^2\mathcal D_{s_n}\) is
negative. The sequential contradiction also gives the uniform threshold
\(V_{\rm act}\). \(\square\)

## C.2. Boundary-conditioned laws and recursive variance mass

In Sections C.2--C.3 the forest need not be canonical; \(V\) denotes the
variance of its global hard-core count at the displayed activity.

Root every component of \(F\), and write \(\operatorname{par}(u)\) for the
parent of a nonroot vertex \(u\). A vertex together with this rooted inherited
context will be understood throughout. Let \(T_u\) be the descendant subtree
rooted at \(u\). Define the three boundary-conditioned partition functions

\[
 P_u(t)=I_{T_u}(t),\qquad
 Q_u(t)=\prod_{v\text{ child of }u}P_v(t),\qquad
 R_u(t)=t\prod_{v\text{ child of }u}Q_v(t).
\]

Thus \(P_u=Q_u+R_u\). The \(P_u\)-state is the unrestricted hard-core law on
\(T_u\) when the parent of \(u\) is absent; the \(Q_u\)-state forces \(u\)
absent; and the \(R_u\)-state forces \(u\) occupied. At the fixed activity
\(z\), set

\[
 p_u=\frac{R_u(z)}{P_u(z)},\qquad q_u=1-p_u.
\]

The rooted recursion for the conditional occupation probability is

\[
 \frac{p_u}{q_u}=z\prod_{v\text{ child of }u}q_v.   \tag{C.6}
\]

For \(0<z<27\), it implies

\[
 q_u>\frac1{28},\qquad p_u<\frac{27}{28}.           \tag{C.7}
\]

Let \(\mu_u^P,\mu_u^Q,\mu_u^R\) and
\(v_u^P,v_u^Q,v_u^R\) denote the count means and variances in these three
states, and define the occupied-versus-absent displacement

\[
 \Delta_u=\mu_u^R-\mu_u^Q.                          \tag{C.8}
\]

Let \(a_u\) be the probability, in the original globally rooted law, that
the parent of \(u\) is absent, with \(a_r=1\) at every component root, and put
\(b_u=1-a_u\). If \(v\) is a child of \(u\), then

\[
 a_v=a_uq_u+b_u=1-a_up_u,\qquad b_v=a_up_u.         \tag{C.9}
\]

In particular, every nonroot vertex satisfies

\[
 a_u>\frac1{28}.                                    \tag{C.10}
\]

Define the **subtree variance mass** and the **vertex variance contribution**
at \(u\) by

\[
 E(u)=a_uv_u^P+b_uv_u^Q,\qquad
 g(u)=a_up_uq_u\Delta_u^2.                          \tag{C.11}
\]

These definitions retain the context in which \(T_u\) occurs inside the
original forest. The conditional-variance identity and the product structure
of the child subtrees give

\[
 v_u^P=q_uv_u^Q+p_uv_u^R+p_uq_u\Delta_u^2,
\]

\[
 v_u^Q=\sum_vv_v^P,\qquad v_u^R=\sum_vv_v^Q.
\]

Substituting (C.9) yields the recursive variance decomposition

\[
 E(u)=g(u)+\sum_{v\text{ child of }u}E(v),\qquad
 \sum_{r\in\mathcal R(F)}E(r)=V,                    \tag{C.12}
\]

where \(\mathcal R(F)\) is the set of component roots. Consequently

\[
 g(u)\le E(u)\le V.                                 \tag{C.13}
\]

Moreover, (C.10) gives the conditional-variance estimate

\[
 v_u^P\le28E(u)                                     \tag{C.14}
\]

for every nonroot \(u\), while at a component root it holds because
\(E(r)=v_r^P\).

## C.3. Large conditional mean differences

We next prove the local estimate that prevents a dominant vertex variance
contribution from being carried by a vanishing occupation probability. Retain
the notation \(a_u,p_u,q_u,\Delta_u,g(u)\), and \(V\) from Section C.2. The
statement applies to a rooted forest under its unrestricted hard-core law,
with a fictitious forced-absent parent at each component root. The conditional
means satisfy

\[
 \Delta_u=1-\sum_{v\text{ child of }u}p_v\Delta_v.   \tag{C.15}
\]

If vertices are ordered with parents before children and

\[
 \eta_u=\xi_u-p_u(1-\xi_{\operatorname{par}(u)}),
\]

then \((\eta_u)\) are martingale differences. Equation (C.15) collects the
coefficient of every occupation indicator in the exact decomposition

\[
 X-\mathbb EX=\sum_u\Delta_u\eta_u.
\]

Since \(\mathbb E\eta_u^2=a_up_uq_u\), orthogonality gives

\[
 V=\operatorname{Var}X=\sum_ug(u).                  \tag{C.16}
\]

For \(b>1\), define the contribution from large conditional mean differences

\[
 G(b)=\sum_{u:|\Delta_u|>b}g(u).                    \tag{C.17}
\]

**Lemma C.2 (large-displacement contribution bound).** Put

\[
 \chi=\frac{784V}{b^2}.
\]

If \(b>1\) and \(\chi<1\), then

\[
 \frac{G(b)}V
 \le \left(\frac b{b-1}\right)^2
       28\chi\log\frac{27}{\chi}.                  \tag{C.18}
\]

In particular, uniformly over all finite forest topologies and all
\(0<z<27\),

\[
 b\longrightarrow\infty,\qquad \frac{V}{b^2}\longrightarrow0
 \quad\Longrightarrow\quad \frac{G(b)}V\longrightarrow0.    \tag{C.19}
\]

**Proof.** For arbitrary real \(y_v\) on the children of \(u\), weighted
Cauchy-Schwarz gives

\[
 \left(\sum_vp_vy_v\right)^2
 \le \left(\sum_v\frac{p_v}{q_v}\right)
      \left(\sum_vp_vq_vy_v^2\right).              \tag{C.20}
\]

All children have parent-absence probability \(a_v=1-a_up_u\). Since

\[
 \frac{a_up_uq_u}{a_v}
 =\frac{a_up_uq_u}{1-a_up_u}\le p_u,
\]

(C.20) implies

\[
 a_up_uq_u\left(\sum_vp_vy_v\right)^2
 \le p_u\left(\sum_v\frac{p_v}{q_v}\right)
      \sum_va_vp_vq_vy_v^2.                        \tag{C.21}
\]

By (C.6), (C.7), and \(t\le-\log(1-t)\) for \(0\le t<1\),

\[
 \sum_v\frac{p_v}{q_v}
 \le28\sum_vp_v
 \le28\sum_v(-\log q_v)
 =28\log\frac{zq_u}{p_u}
 \le28\log\frac{27}{p_u}.                         \tag{C.22}
\]

If \(|\Delta_u|>b\), then (C.15) gives

\[
 \left|\sum_vp_v\Delta_v\right|=|1-\Delta_u|
 \ge\left(1-\frac1b\right)|\Delta_u|.             \tag{C.23}
\]

Also \(a_u,q_u>1/28\), with \(a_u=1\) at a component root, so
(C.16) implies

\[
 \frac{p_u\Delta_u^2}{784}\le g(u)\le V,
 \qquad p_u<\frac{784V}{b^2}=\chi.                 \tag{C.24}
\]

The function \(t\mapsto t\log(27/t)\) is increasing on \((0,1)\).
Applying (C.21)--(C.24) with \(y_v=\Delta_v\) therefore gives, for every vertex
counted by \(G(b)\),

\[
 g(u)
 \le\left(\frac b{b-1}\right)^2
      28\chi\log\frac{27}{\chi}
      \sum_{v\text{ child of }u}g(v).              \tag{C.25}
\]

After summation, every child term on the right occurs at most once, because a
vertex has a unique parent. The double sum is at most \(V\) by (C.16), which
proves (C.18). The right side of (C.18) tends to zero under the hypotheses
of (C.19). \(\square\)

## C.4. Occupation and displacement bounds at a dominant vertex

**Theorem C.3 (bounds at a dominant vertex).** Fix \(c>0\). There are
\(\rho(c)>0\) and \(V_{\rm bal}(c)<\infty\) such that the following holds.
In any canonical first-recovery state at activity \(0<z<27\), after rooting
each component arbitrarily, if a vertex \(u\) satisfies

\[
 V\ge V_{\rm bal}(c),\qquad g(u)\ge cV,             \tag{C.26}
\]

then

\[
 p_u\ge\rho(c),                                    \tag{C.27}
\]

and

\[
 4cV\le\Delta_u^2\le\frac{784}{\rho(c)}V.          \tag{C.28}
\]

Together with \(q_u>1/28\), (C.27) says that the two local boundary states are
uniformly balanced.

**Proof.** Suppose that no uniform lower bound in (C.27) exists. By
contradiction along a sequence, there are canonical first-recovery states, chosen
component rootings, and vertices \(u_n\) with

\[
 V_n\to\infty,\qquad g(u_n)\ge cV_n,\qquad p_{u_n}\to0.       \tag{C.29}
\]

Apply Lemma C.2 to the local \(P_{u_n}\)-state, without changing the
activity or giving that state any global recovery property. Write
\(v=v_{u_n}^P\) and \(\Delta=\Delta_{u_n}\). Its root variance contribution is

\[
 \widetilde g=p_{u_n}q_{u_n}\Delta^2
 =\frac{g(u_n)}{a_{u_n}}\ge cV_n,                  \tag{C.30}
\]

while (C.13)--(C.14) give

\[
 v\le28E(u_n)\le28V_n.                             \tag{C.31}
\]

Set \(b=|\Delta|/2\). From (C.30) and \(p_{u_n}q_{u_n}\le1/4\),
\(b\to\infty\). Moreover,

\[
 \frac{784v}{b^2}
 =\frac{3136v}{\Delta^2}
 \le\frac{87808V_n}{\Delta^2}
 \le\frac{87808}{c}p_{u_n}q_{u_n}\longrightarrow0.          \tag{C.32}
\]

Thus Lemma C.2 applies for all sufficiently large \(n\) and gives
\(G(b)/v\to0\). The local root itself has gap \(|\Delta|>b\), however, so

\[
 \frac{G(b)}v\ge\frac{\widetilde g}{v}\ge\frac c{28},        \tag{C.33}
\]

a contradiction. This proves a uniform \(\rho(c)>0\); otherwise choosing
\(V_n\ge n\) and \(p_{u_n}<1/n\) would reproduce (C.29).

Finally, \(a_up_uq_u\le1/4\), so (C.26) gives

\[
 \Delta_u^2\ge4cV.
\]

On the other hand, (C.7), (C.10), and (C.27) imply
\(a_up_uq_u\ge\rho(c)/784\), with a component-root case even stronger. Since
\(g(u)\le E(u)\le V\),

\[
 \Delta_u^2=\frac{g(u)}{a_up_uq_u}
 \le\frac{784}{\rho(c)}V.
\]

This proves (C.28). \(\square\)

In particular, if Theorem 4.1 supplies \(u\) with
\(g(u)\ge\kappa_{27}V\), Theorem C.3 applies with \(c=\kappa_{27}\). The
constant \(\kappa_{27}>0\) is the one in Theorem 4.1, so the resulting
constants depend only on the fixed activity cap.

## C.5. Addable vertices, low outdegree, and bipartition conditioning

We now turn to a canonical first-recovery state with \(0<z<27\) and
\(V\ge V_{\rm act}\). By Lemma C.1, throughout this section we may assume

\[
 \frac32<z<27.                                      \tag{C.34}
\]

For an independent set \(I\), a vertex is **addable** if it does not belong
to \(I\) and has no neighbor in \(I\). Let

\[
 A=A(I)=\#\{v\notin I:N(v)\cap I=\varnothing\}.
\]

For a uniformly chosen independent \(k\)-set, write \(A_k\) for its number
of addable vertices and \(\mu_k=\mathbb E A_k\). Counting pairs
\((I,v)\), where \(I\) has size \(k\) and \(v\) is addable to \(I\), gives the
exact insertion identity

\[
 i_k\mu_k=(k+1)i_{k+1}.                             \tag{C.35}
\]

Averaging (C.35) under the hard-core law gives the same-activity identity

\[
 z\mathbb EA=\mathbb EX=s.                         \tag{C.36}
\]

At the first-recovery index, (C.1) and (C.35) give the stronger conditional
expectation identity

\[
 \mathbb E[A\mid X=s]
 =(s+1)\frac{i_{s+1}}{i_s}>s+1.                    \tag{C.37}
\]

We next record the order bound that is needed both for Hoeffding's inequality
and for the upper variance estimate.

**Lemma C.4 (low-outdegree order bound).** Under (C.34),

\[
 N+1<C_*s,\qquad C_*:=\frac{3304}{3}.               \tag{C.38}
\]

**Proof.** Let \(q\ge1\) be the number of components. A componentwise rooted
forest has \(N-q\) child edges, so the number of vertices with at least two
children is at most \((N-q)/2\). Hence at least
\((N+q)/2\ge(N+1)/2\) vertices have at most one child.

For a vertex with at most one child, (C.6), (C.7), and \(z>3/2\) imply

\[
 \frac{p_u}{q_u}>\frac3{56},\qquad p_u>\frac3{59}.
\]

The probability that its parent is absent is greater than \(1/28\), except
at a component root where it equals one. Hence its global occupation probability is
greater than \(3/1652\). Summing occupation probabilities over the
\((N+1)/2\) such vertices gives

\[
 s=\mathbb EX>\frac{3(N+1)}{3304},
\]

which is (C.38). \(\square\)

Two immediate consequences are

\[
 N<C_*s,
 \qquad
 V\le\mathbb EX^2\le N\mathbb EX=Ns<C_*s^2.        \tag{C.39}
\]

The second inequality uses \(0\le X\le N\), hence \(X^2\le NX\).

Let \(V(F)=L\sqcup R\) be a bipartition of the forest and set

\[
 \theta=\frac{z}{1+z},\qquad \bar q=1-\theta=\frac1{1+z}.
\]

For \(C\in\{L,R\}\), let \(D\) be the opposite color and let
\(\mathcal F_C=\sigma(\xi_u:u\in C)\). Given \(\mathcal F_C\), write
\(K_C=\sum_{u\in C}\xi_u\), and let \(a_C\) be the number of vertices in
\(D\) having no occupied neighbor in \(C\). The vertices counted by \(a_C\)
are mutually nonadjacent, and their occupations are conditionally independent
Bernoulli variables with parameter \(\theta\). Therefore

\[
 X\mid\mathcal F_C=K_C+\operatorname{Bin}(a_C,\theta),        \tag{C.40}
\]

\[
 M_C:=\mathbb E[X\mid\mathcal F_C]=K_C+\theta a_C,\qquad
 W_C:=\operatorname{Var}(X\mid\mathcal F_C)
 =\theta\bar q\,a_C.                                \tag{C.41}
\]

These are identities in the original global Gibbs law.

For each vertex \(v\), let \(A_v\) be its addability indicator and put

\[
 B_v=\xi_v+A_v,\qquad h_v=\xi_v-\theta B_v.
\]

Thus \(B_v\) indicates that every neighbor of \(v\) is absent. From
(C.40)--(C.41), the two color residuals
\(\varepsilon_C=X-M_C\) satisfy

\[
 \varepsilon_L=\sum_{v\in R}h_v,\qquad
 \varepsilon_R=\sum_{u\in L}h_u,
\]

and hence the exact pointwise identity

\[
 \varepsilon_L+\varepsilon_R
 =X-\theta\sum_vB_v
 =\frac{X-zA}{1+z}.                                 \tag{C.42}
\]

There is one further consequence of the same single-site toggle. If
\(s_R=\mathbb E\sum_{v\in R}\xi_v\), then

\[
 \Pr(\xi_v=1)=\theta\Pr(B_v=1)\qquad(v\in R),
\]

so

\[
 \mathbb EW_L=\bar q\,s_R.                         \tag{C.43}
\]

The analogous formula holds with \(L\) and \(R\) interchanged.

## C.6. An exponential upper bound at the mean

**Lemma C.5 (probability at the mean).** There are constants \(V_h<\infty\),
\(C_h<\infty\), and \(\gamma_0>0\), depending only on the activity cap, such
that every canonical first-recovery state with \(0<z<27\) and \(V\ge V_h\)
satisfies

\[
 \pi(0)=\Pr(X=s)\le C_he^{-\gamma_0s}.              \tag{C.44}
\]

One may take

\[
 C_h=12C_*,\qquad \gamma_0=\frac1{25088C_*}.        \tag{C.45}
\]

**Proof.** Take \(V_h=V_{\rm act}\), so that (C.34) holds for every state
under consideration. Since \(A\le N-X\), (C.37) implies

\[
 N-s>s+1,
\]

and, because \(N\) and \(s\) are integers,

\[
 N\ge2s+2.                                         \tag{C.46}
\]

Let

\[
 \delta=\Pr(A\ge5s/6\mid X=s).
\]

Using (C.37) and then (C.38),

\[
 s+1<\mathbb E[A\mid X=s]
 \le\frac{5s}{6}+N\delta
\]

gives

\[
 \delta>\frac{s}{6N}>\frac1{6C_*}.                 \tag{C.47}
\]

On the event \(\{X=s,A\ge5s/6\}\), (C.34) and (C.42) give

\[
 \varepsilon_L+\varepsilon_R
 =\frac{s-zA}{1+z}< -\frac{s}{112}.                \tag{C.48}
\]

Thus at least one color has
\(\varepsilon_C<-s/224\), equivalently \(M_C-s>s/224\). By (C.47) and
pigeonholing the two colors, there is one fixed
\(C\in\{L,R\}\) such that

\[
 \Pr(M_C-s>s/224\mid X=s)>\frac1{12C_*}.           \tag{C.49}
\]

For an \(\mathcal F_C\)-environment in the event in (C.49), (C.40) and the
lower-tail form of Hoeffding's inequality [Hoe63] imply

\[
\begin{aligned}
 \Pr(X=s\mid\mathcal F_C)
 &\le \exp\left[-\frac{2(s/224)^2}{a_C}\right]\\
 &\le \exp\left[-\frac{s}{25088C_*}\right],        \tag{C.50}
\end{aligned}
\]

because \(a_C\le N<C_*s\). If \(a_C=0\), the left side is zero on this
event, so the same bound holds by convention.

Let \(\mathcal E_C=\{M_C-s>s/224\}\). Bayes' formula and (C.50) give

\[
\begin{aligned}
 \Pr(\mathcal E_C\mid X=s)
 &=\frac{\mathbb E[\mathbf1_{\mathcal E_C}
       \Pr(X=s\mid\mathcal F_C)]}{\pi(0)}\\
 &\le\frac{e^{-s/(25088C_*)}}{\pi(0)}.
\end{aligned}
\]

Combining this with (C.49) proves (C.44)--(C.45). \(\square\)

## C.7. A conditional-binomial lower bound and the variance lower bound

The lower estimate complementary to the preceding Hoeffding bound is
the following finite, uniform local bound.

**Lemma C.6 (uniform binomial mass lower bound).** There are constants
\(c_b,C_b>0\) such that the following holds. Let \(a\) be a nonnegative
integer, let \(K,s\in\mathbb Z\), and let

\[
 \frac35\le\theta\le\frac{27}{28},\qquad
 Y=K+\operatorname{Bin}(a,\theta),\qquad
 M=\mathbb EY,\qquad W=\operatorname{Var}Y.
\]

If \(H\ge1\), \(W\ge4H\), and

\[
 (M-s)^2\le HW,
\]

then

\[
 \Pr(Y=s)\ge c_bW^{-1/2}e^{-C_bH}.                 \tag{C.51}
\]

**Proof.** Since \(W\ge4\), one has \(a>0\). Put \(k=s-K\), \(r=k/a\), and
\(t=k-a\theta=s-M\). The assumptions imply

\[
 |t|\le\sqrt{HW}\le W/2=a\theta(1-\theta)/2.
\]

Consequently

\[
 \frac{12}{25}\le r\le\frac{1539}{1568}<1.
\]

Indeed, \(|r-\theta|\le\theta(1-\theta)/2\), and the two extrema follow at
the endpoints of \([3/5,27/28]\).  In particular \(1\le k\le a-1\).
For every integer \(n\ge1\), the elementary Stirling inequalities

\[
 \sqrt{2\pi}\,n^{n+1/2}e^{-n}
 \le n!\le e\,n^{n+1/2}e^{-n}
\]

give, with the universal constant \(c_0=\sqrt{2\pi}/e^2\),

\[
 \Pr(\operatorname{Bin}(a,\theta)=k)
 \ge \frac{c_0}{\sqrt{a r(1-r)}}
      \exp\{-aD(r\Vert\theta)\},                   \tag{C.52}
\]

where

\[
 D(r\Vert\theta)
 =r\log\frac r\theta+(1-r)\log\frac{1-r}{1-\theta}
\]

is the Bernoulli relative entropy.  Both \(r\) and \(\theta\), and therefore
the segment joining them, lie in the fixed interval
\(J=[12/25,1539/1568]\). Since

\[
 \frac{\partial^2}{\partial x^2}D(x\Vert\theta)
 =\frac1{x(1-x)},
\]

Taylor's theorem, uniformly on \(J\), gives

\[
 aD(r\Vert\theta)\le C\frac{t^2}{W}\le CH.
\]

Here we used \(r-\theta=t/a\) and
\(a^{-1}=\theta(1-\theta)/W\).  On the displayed compact intervals the
ratio \(r(1-r)/[\theta(1-\theta)]\) is bounded above and below by positive
absolute constants. Thus \(ar(1-r)\) is uniformly comparable to \(W\).
Substitution in (C.52) proves (C.51). \(\square\)

We can now complete the second main result.

**Theorem C.7 (size and variance at first recovery).** There are
positive constants \(c_V,C_V,c_N,C_N\) and \(V_{\rm sc}<\infty\) such that
every canonical first-recovery state with \(0<z<27\) and
\(V\ge V_{\rm sc}\) satisfies

\[
 c_Vs^2\le V\le C_Vs^2,
 \qquad c_Ns\le N\le C_Ns.                         \tag{C.53}
\]

In particular,

\[
 V=\Theta(s^2),\qquad N=\Theta(s),\qquad
 s,N=\Theta(\sqrt V)                               \tag{C.54}
\]

uniformly over all canonical first-recovery states satisfying \(0<z<27\)
and \(V\ge V_{\rm sc}\).

**Proof.** The upper bounds have already been proved: (C.38)--(C.39) give

\[
 N<C_*s,\qquad V<C_*s^2.                           \tag{C.55}
\]

It remains to prove the quadratic lower bound for \(V\).

Orient the bipartition so that the unrevealed color \(R\) has mean occupation
\(s_R\ge s/2\), and reveal \(L\). By (C.34),
\(\bar q=1/(1+z)>1/28\), so (C.43) gives

\[
 \mathbb EW_L>\frac{s}{56}.                        \tag{C.56}
\]

Also \(0\le W_L\le a_L/4\le N/4<C_*s/4\). Therefore

\[
 \Pr(W_L\ge s/112)
 \ge\delta_*:=\frac1{28C_*}.                       \tag{C.57}
\]

Indeed, if the probability on the left is \(q\), then

\[
 \mathbb EW_L\le\frac{s}{112}+\frac{C_*s}{4}q,
\]

and (C.56) yields (C.57).

Let \(c_b,C_b\) be supplied by Lemma C.6 and define

\[
 \gamma=\min\left\{\frac{\gamma_0}{2C_b},\frac1{448}\right\},
 \qquad H=\gamma s.                                \tag{C.58}
\]

By (C.55), \(s\to\infty\) uniformly as \(V\to\infty\). Choose
\(V_H\ge V_h\) so that \(V\ge V_H\) implies \(H\ge1\). For either color
\(D\in\{L,R\}\), put

\[
 \mathcal B_D=
 \{W_D\ge4H,\ (M_D-s)^2\le HW_D\}.
\]

Applying Lemma C.6 conditionally in (C.40), and using
\(W_D\le C_*s/4\), gives

\[
\begin{aligned}
 \pi(0)
 &=\mathbb E\Pr(X=s\mid\mathcal F_D)\\
 &\ge c_be^{-C_bH}\mathbb E[\mathbf1_{\mathcal B_D}W_D^{-1/2}]\\
 &\ge \frac{2c_b}{\sqrt{C_*s}}e^{-C_bH}
        \Pr(\mathcal B_D).
\end{aligned}                                      \tag{C.59}
\]

The exponential center bound (C.44), together with (C.58), now yields

\[
 \Pr(\mathcal B_D)
 \le C\sqrt{s}\,e^{-(\gamma_0-C_b\gamma)s}=o(1).    \tag{C.60}
\]

Because \(\gamma_0-C_b\gamma\ge\gamma_0/2\), the bound in (C.60) tends to
zero uniformly as \(V\to\infty\). Fix \(V_{\rm fb}\ge V_H\) such that its
right-hand side is at most \(\delta_*/2\) whenever \(V\ge V_{\rm fb}\).
Because \(\gamma\le1/448\), one has \(s/112\ge4H\). Combining
(C.57) and (C.60), every state with \(V\ge V_{\rm fb}\) satisfies, with
probability at least \(\delta_*/2\),

\[
 W_L\ge\frac{s}{112},\qquad
 (M_L-s)^2>HW_L\ge\frac{\gamma s^2}{112}.          \tag{C.61}
\]

Since \(\mathbb EM_L=\mathbb EX=s\), the law of total variance gives

\[
\begin{aligned}
 V&=\mathbb EW_L+\operatorname{Var}(M_L)
    \ge\operatorname{Var}(M_L)\\
  &=\mathbb E(M_L-s)^2
    \ge\frac{\delta_*\gamma}{224}s^2.              \tag{C.62}
\end{aligned}
\]

Thus one may take

\[
 c_V=\frac{\delta_*\gamma}{224},\qquad C_V=C_*.
\]

Finally, (C.46) and (C.55) in particular give

\[
 s\le N<C_*s,
\]

so \(c_N=1\) and \(C_N=C_*\) are valid. Taking
\(V_{\rm sc}=V_{\rm fb}\) completes the proof of (C.53). The two estimates
in (C.53) imply (C.54). \(\square\)

# Appendix D. A vertex carrying a fixed variance fraction

This appendix proves the fixed-variance-fraction theorem used in
Theorem 4.1. The
theorem holds on the full componentwise rooted forest, for every choice of
one root in each component. All
conditional occupation probabilities, boundary-conditioned laws, and
variances below belong to the
original forest at its canonical activity. In particular, no component or
descendant subtree is assigned a canonical activity or a first-recovery
hypothesis.

The proof is by contradiction. Lemma D.4 excludes a diffuse exposed antichain
carrying a fixed proportion of the variance. Lemma D.5 therefore reduces the
variance to a finite-branch rooted subforest. Lemmas D.6 and D.7 verify the
Lindeberg and predictable-quadratic-variation hypotheses there, and
Proposition D.8 combines the resulting martingale central limit theorem with
the full-domain Fourier envelope of Theorem A.1. The limiting positive central
curvature contradicts first recovery and yields Theorem D.1.

## D.1. Boundary-conditioned laws and recursive variance mass

Let

\[
 I_F(t)=\sum_k i_k(F)t^k
\]

be the independence polynomial of a finite forest \(F\). Suppose its
coefficient sequence falls and later rises, and define

\[
 m=\min\{k:i_k>i_{k+1}\},\qquad
 s=\min\{k>m:i_k<i_{k+1}\}.
\]

Thus \(s\) is the first-recovery index and
\(i_s^2<i_{s-1}i_{s+1}\).  The canonical activity is the unique \(z>0\)
for which the hard-core law

\[
 \Pr_z(\xi)=\frac{z^{\sum_{u\in F}\xi_u}}{I_F(z)}
 \mathbf 1_{\{\{u:\xi_u=1\}\text{ is independent}\}}
\]

satisfies

\[
 X=\sum_{u\in F}\xi_u,\qquad
 \mathbb E_zX=s,\qquad V=\operatorname{Var}_zX.
 \tag{D.1}
\]

For \(j\in\mathbb Z\), put

\[
 \pi(j)=\Pr_z(X=s+j).
\]

The activity factors cancel from the adjacent log-concavity difference, and
hence
every canonical first-recovery state satisfies

\[
 \pi(0)^2-\pi(-1)\pi(1)<0.
 \tag{D.2}
\]

Fix an arbitrary root in each component of \(F\), and let
\(\mathcal R(F)\) be the set of component roots. For a vertex \(u\), let
\(T_u\) be its descendant subtree and let \(\operatorname{ch}(u)\) be
its set of children. Every component root has a virtual parent fixed to be
absent. Conditional
on the parent of \(u\) being absent, write

\[
 p_u=\Pr_z(\xi_u=1\mid \xi_{\operatorname{par}(u)}=0),
 \qquad q_u=1-p_u.
 \tag{D.3}
\]

If \(R_u=p_u/q_u\) denotes the occupation odds, the rooted-tree recursion is

\[
 R_u=z\prod_{v\in\operatorname{ch}(u)}q_v.
 \tag{D.4}
\]

Throughout the appendix \(0<z<27\).  Consequently,

\[
 0<p_u<\overline p_{27}:=\frac{27}{28},\qquad q_u>\frac1{28}.
 \tag{D.5}
\]

Let \(P_u,Q_u,R_u^{\rm occ}\) denote the laws of the occupation count in
\(T_u\) when the root \(u\) is, respectively, free, forced absent, and
forced occupied.  Superscripts \(P,Q,R\) on means and variances refer to
these three boundary-conditioned laws. Define the conditional mean difference

\[
 \Delta_u=\mu_u^R-\mu_u^Q.
\]

Conditioning first at \(u\) and then at its children gives

\[
 \Delta_u=1-\sum_{v\in\operatorname{ch}(u)}p_v\Delta_v.
 \tag{D.6}
\]

The parent-state probabilities are

\[
 a_u=\Pr_z(\xi_{\operatorname{par}(u)}=0),\qquad
 b_u=1-a_u,
 \tag{D.7}
\]

with \(a_r=1\) and \(b_r=0\) for every \(r\in\mathcal R(F)\). If \(v\) is a
child of \(u\), then

\[
 a_v=a_uq_u+b_u=1-a_up_u>\frac1{28},
 \qquad b_v=a_up_u.
 \tag{D.8}
\]

Define the **vertex variance contribution** and **subtree variance mass** by

\[
 g(u)=a_up_uq_u\Delta_u^2,
 \qquad
 E(u)=a_uv_u^P+b_uv_u^Q.
 \tag{D.9}
\]

At a component root \(r\), \(E(r)=v_r^P\), and component independence gives
\(\sum_{r\in\mathcal R(F)}E(r)=V\).

**Recursive variance decomposition.** For every vertex \(u\),

\[
 v_u^P=q_uv_u^Q+p_uv_u^R+p_uq_u\Delta_u^2,
 \qquad
 v_u^Q=\sum_{v\in\operatorname{ch}(u)}v_v^P,
 \qquad
 v_u^R=\sum_{v\in\operatorname{ch}(u)}v_v^Q.
 \tag{D.10}
\]

Moreover,

\[
 v_u^P\le 28E(u),\qquad v_u^Q\le784E(u),
 \tag{D.11}
\]

and the exact recursive decomposition is

\[
 E(u)=g(u)+\sum_{v\in\operatorname{ch}(u)}E(v).
 \tag{D.12}
\]

Consequently,

\[
 E(u)=\sum_{v\succeq u}g(v),\qquad
 V=\sum_{u\in F}g(u).
 \tag{D.13}
\]

Here \(v\succeq u\) means that \(v\) is a descendant of \(u\), with
\(u\succeq u\).

If \(A\) is an antichain, then its descendant subtrees are disjoint and

\[
 \sum_{u\in A}E(u)\le V.
 \tag{D.14}
\]

*Proof.*  The first identity in (D.10) is the conditional-variance formula
for the mixture \(P_u=q_uQ_u+p_uR_u^{\rm occ}\).  Under \(Q_u\), the child
subtrees have their independent \(P_v\) laws; under \(R_u^{\rm occ}\), they
have their independent \(Q_v\) laws.  This proves all of (D.10).

The mixture identity gives \(v_u^P\ge q_uv_u^Q\). Also \(a_u\ge1/28\),
including every component root, by (D.8). Therefore

\[
 v_u^P\le a_u^{-1}E(u)\le28E(u),\qquad
 v_u^Q\le q_u^{-1}v_u^P\le784E(u),
\]

which is (D.11).  Substituting (D.10) and (D.8) into (D.9) gives

\[
\begin{aligned}
 \sum_{v\in\operatorname{ch}(u)}E(v)
 &=\sum_v\bigl[(a_uq_u+b_u)v_v^P+a_up_uv_v^Q\bigr]\\
 &=a_u\bigl(v_u^P-p_uq_u\Delta_u^2\bigr)+b_uv_u^Q
 =E(u)-g(u),
\end{aligned}
\]

proving (D.12).  Iteration to the leaves proves (D.13), and summing (D.13)
over disjoint descendant subtrees proves (D.14).  \(\square\)

We can now state the full-forest theorem.

**Theorem D.1 (a vertex carrying a fixed variance fraction).** There are constants
\(\kappa_{27}>0\) and \(V_{27}<\infty\) such that every canonical
first-recovery state with \(0<z<27\) and \(V\ge V_{27}\) has the following
property: for every choice of one root in each component of \(F\), some
vertex \(u\in F\) satisfies

\[
 g(u)\ge\kappa_{27}V.
 \tag{D.15}
\]

The factor \(a_u\) in \(g(u)\) is always the one induced by the
selected componentwise rooting of the original state.

## D.2. Martingale decomposition of the occupation count

For every vertex \(u\), define

\[
 \eta_u=\xi_u-p_u(1-\xi_{\operatorname{par}(u)}),
 \tag{D.16}
\]

using the virtual absent parent at every component root.

**Lemma D.2 (martingale projection).** Let \(S\subseteq F\) be ancestor-closed in
every rooted component.
Then

\[
 X-s=\sum_{u\in F}\Delta_u\eta_u,
 \qquad
 Z_S:=\mathbb E[X-s\mid\xi_S]
 =\sum_{u\in S}\Delta_u\eta_u.
 \tag{D.17}
\]

Moreover,

\[
 \operatorname{Var}(Z_S)=\sum_{u\in S}g(u),\qquad
 \mathbb E[(X-s-Z_S)^2]=V-\sum_{u\in S}g(u).
 \tag{D.18}
\]

*Proof.*  List the vertices in a parent-before-child order and let
\(\mathcal F_k\) be the sigma-field generated by the first \(k\) occupation
variables, after concatenating arbitrary component orders. If \(u\) is the
\(k\)-th vertex, the spatial Markov property of the forest and
independence of its components give

\[
 \mathbb E[\eta_u\mid\mathcal F_{k-1}]=0,
 \qquad
 \mathbb E\eta_u^2=a_up_uq_u.
 \tag{D.19}
\]

Thus the weighted variables \(\Delta_u\eta_u\) are martingale differences.
On expanding their sum, the coefficient of \(\xi_u\) is

\[
 \Delta_u+\sum_{v\in\operatorname{ch}(u)}p_v\Delta_v=1
\]

by (D.6).  The remaining constant is \(-\mathbb EX=-s\), because the sum is
centered.  This proves the first identity in (D.17).

Since \(S\) is ancestor-closed, a parent-before-child ordering can list all
of \(S\) first.  Every omitted term is then a future martingale difference,
so conditional expectation proves the second identity in (D.17).
Orthogonality, (D.9), and (D.19) prove the first identity in (D.18); the
second is the Pythagorean identity for conditional expectation.  \(\square\)

## D.3. Diffuse exposed antichains

If \(D\subseteq F\) is ancestor-closed in every rooted component, its exposed
boundary is

\[
 \partial^+D=\{u\notin D:u\in\mathcal R(F)
                  \text{ or }\operatorname{par}(u)\in D\}.
 \tag{D.20}
\]

An antichain \(A\) is called an **exposed antichain** if
\(A=\partial^+D\) for some set \(D\) that is ancestor-closed in every rooted
component. Thus \(A\) consists of the roots of the descendant components cut
off from \(D\), together with the roots of any original components disjoint
from \(D\). Its boundary-conditioned laws and weights are always inherited
from the original rooted hard-core measure. For the nonnegative quantities
below, a maximum over the empty set is defined to be zero.

We will also use the full-domain Fourier envelope from Appendix A,
Theorem A.1.  There are constants \(c_{27}>0\) and
\(\alpha_{27}\in(0,1)\) such that every finite forest at activity \(0<z<27\)
satisfies

\[
 \left|\mathbb E_z e^{\mathrm i\theta(X-\mathbb EX)}\right|
 \le\exp\left\{-c_{27}\min\left(
 V\theta^2,(V\theta^2)^{\alpha_{27}}\right)\right\},
 \qquad |\theta|\le\pi.
 \tag{D.21}
\]

**Lemma D.3 (antichain factorization).** Let \(A\) be an exposed
antichain in a rooted forest, and reveal all occupation variables
outside \(\bigcup_{u\in A}T_u\).  Conditionally on the revealed
sigma-field, the counts in the subtrees \(T_u\), \(u\in A\), are
independent. The count in \(T_u\) has its \(P_u\) law when the
parent of \(u\) is absent and its \(Q_u\) law when that parent is
occupied. For a component root in \(A\), the virtual parent is absent and the
subtree count is deterministically in its \(P_u\) state. In all cases the
unconditional probabilities of the two alternatives are \(a_u\) and \(b_u\).

*Proof.* Cut the edge immediately above every nonroot member of \(A\);
members that are component roots already begin disjoint components. The
hard-core weight then factors over the resulting descendant components once
the occupations in their complement, and hence all nontrivial boundary parent
states, have been fixed. No parameter changes under this conditioning. The
last assertion is exactly the probabilistic definition (D.7), including
\(a_u=1,b_u=0\) at a component root.
\(\square\)

**Lemma D.4 (diffuse-antichain exclusion).**  Let
\((F_n,s_n,z_n,V_n)\) be a canonical first-recovery sequence with
\(0<z_n<27\), \(V_n\to\infty\), and an arbitrary selected componentwise
rooting for each \(n\).  For every sequence of exposed antichains \(A_n\),

\[
 \max_{u\in A_n}\frac{E_n(u)}{V_n}\longrightarrow0
 \quad\Longrightarrow\quad
 \frac1{V_n}\sum_{u\in A_n}E_n(u)\longrightarrow0.
 \tag{D.22}
\]

*Proof.*  Suppose otherwise.  After passing to a subsequence, there is a
fixed \(c>0\) such that, with

\[
 L_n=\sum_{u\in A_n}E_n(u),\qquad
 \beta_n=\max_{u\in A_n}\frac{E_n(u)}{V_n},
 \tag{D.23}
\]

one has \(L_n\ge cV_n\) and \(\beta_n\to0\).  By (D.14), \(L_n\le V_n\).

Appendix A, Lemma A.3, applied with activity ceiling \(27\), gives a constant
\(K_4<\infty\) such that every \(P\)- and \(Q\)-boundary-conditioned law
satisfies

\[
 \mathbb E|X_u^C-\mu_u^C|^4
 \le K_4v_u^C(1+v_u^C),\qquad C\in\{P,Q\}.
 \tag{D.24}
\]

Indeed, the \(P\)-law is the hard-core law on the tree \(T_u\), and
the \(Q\)-law is the hard-core law on the forest below the forced
absent root.  Both retain the original activity.

Reveal every occupation variable outside the disjoint union of the
descendant subtrees \(T_u\), \(u\in A_n\), and denote the resulting
sigma-field by \(\mathcal G_n\).  By Lemma D.3, the selected subtree counts
are conditionally independent \(P/Q\) blocks. If

\[
 M_n=\mathbb E[X_n\mid\mathcal G_n],
\]

then

\[
 X_n-M_n=\sum_{u\in A_n}Z_{n,u},\qquad
 W_n=\sum_{u\in A_n}\sigma_{n,u}^2,
 \tag{D.25}
\]

where, conditionally on \(\mathcal G_n\), the \(Z_{n,u}\) are independent
and centered, and
\(\sigma_{n,u}^2=\operatorname{Var}(Z_{n,u}\mid\mathcal G_n)\).
The probabilities of the two parent states are exactly \(a_u\) and \(b_u\),
so

\[
 \mathbb EW_n=L_n\ge cV_n,
 \qquad
 \operatorname{Var}(M_n)=V_n-L_n\le V_n.
 \tag{D.26}
\]

Equations (D.11) and (D.14) also give, for every revealed configuration,

\[
 0\le W_n\le C_{\mathrm D}L_n\le C_{\mathrm D}V_n,
 \qquad
 \max_{u\in A_n}\frac{\sigma_{n,u}^2}{V_n}
 \le C_{\mathrm D}\beta_n,
 \qquad C_{\mathrm D}:=784.
 \tag{D.27}
\]

For fixed \(\varepsilon>0\), define the conditional Lindeberg sum

\[
 \Lambda_n(\varepsilon)=\frac1{V_n}\sum_{u\in A_n}
 \mathbb E\left[Z_{n,u}^2;
 |Z_{n,u}|>\varepsilon\sqrt{V_n}\mid\mathcal G_n\right].
 \tag{D.28}
\]

Fourth-moment Markov, (D.11), and (D.24) imply

\[
\begin{aligned}
 \mathbb E\Lambda_n(\varepsilon)
 &\le \frac{K_4}{\varepsilon^2V_n^2}
 \sum_{u\in A_n}\left[
 a_uv_u^P(1+v_u^P)+b_uv_u^Q(1+v_u^Q)\right]\\
 &\le \frac{K_4}{\varepsilon^2}
 \left(\frac1{V_n}+C_{\mathrm D}\beta_n\right)
 \longrightarrow0.
\end{aligned}
 \tag{D.29}
\]

For the second inequality, (D.11) gives
\[
 a_u(v_u^P)^2+b_u(v_u^Q)^2
 \le C_{\mathrm D}E_n(u)^2,
\]
while
\[
 \sum_{u\in A_n}E_n(u)^2
 \le\left(\max_{u\in A_n}E_n(u)\right)L_n
 \le\beta_nV_n^2.
\]
Thus every term in the aggregate estimate is controlled in the original
inherited normalization. This is the required aggregate conditional
Lindeberg estimate.

Let

\[
 \Psi_n(t\mid\mathcal G_n)
 =\mathbb E\left[
 e^{\mathrm it(X_n-M_n)/\sqrt{V_n}}\mid\mathcal G_n\right].
\]

For every fixed \(t\in\mathbb R\),

\[
 \mathbb E\left|
 \Psi_n(t\mid\mathcal G_n)
 -\exp\left(-\frac{t^2W_n}{2V_n}\right)
 \right|\longrightarrow0.
 \tag{D.30}
\]

To prove this, Taylor-expand each centered conditional factor:

\[
 \mathbb E(e^{\mathrm itZ_{n,u}/\sqrt{V_n}}\mid\mathcal G_n)
 =1-\frac{t^2\sigma_{n,u}^2}{2V_n}+r_{n,u}(t).
\]

For every auxiliary \(\varepsilon>0\), the cubic remainder on
\(|Z_{n,u}|\le\varepsilon\sqrt{V_n}\) and the quadratic bound on its
complement give

\[
 \sum_{u\in A_n}|r_{n,u}(t)|
 \le C_t\left(
 \varepsilon\frac{W_n}{V_n}+\Lambda_n(\varepsilon)\right).
 \tag{D.31}
\]

Taking expectations, using (D.27) and (D.29), then sending first
\(n\to\infty\) and then \(\varepsilon\downarrow0\), makes the right-hand
side negligible in \(L^1\).  In addition,

\[
 \sum_{u\in A_n}
 \left(\frac{t^2\sigma_{n,u}^2}{2V_n}\right)^2
 \le\frac{t^4}{4}
 \left(\max_{u\in A_n}\frac{\sigma_{n,u}^2}{V_n}\right)
 \frac{W_n}{V_n}\longrightarrow0
 \tag{D.32}
\]

uniformly in the revealed configuration.  The logarithmic expansion of the
product of the quadratic factors now proves (D.30).

Set \(\omega=c/2\).  From (D.26)--(D.27),

\[
 \Pr(W_n\ge\omega V_n)\ge
 p_c:=\frac{c/2}{C_{\mathrm D}-c/2}>0.
 \tag{D.33}
\]

Indeed, if \(p\) is the probability on the left, then
\(c\le\mathbb E(W_n/V_n)\le\omega+(C_{\mathrm D}-\omega)p\).  Since
\(\mathbb EM_n=\mathbb EX_n\), (D.26) and Chebyshev's inequality give

\[
 \Pr(|M_n-\mathbb EX_n|>B\sqrt{V_n})\le B^{-2}.
\]

Choose a fixed \(B\) with \(B^{-2}<p_c/2\), and define the
\(\mathcal G_n\)-measurable event

\[
 \mathcal A_n=\left\{
 \frac{W_n}{V_n}\in[\omega,C_{\mathrm D}],\quad
 \frac{|M_n-\mathbb EX_n|}{\sqrt{V_n}}\le B
 \right\}.
\]

Then

\[
 \Pr(\mathcal A_n)\ge p_c/2.
 \tag{D.34}
\]

Apply Appendix B, Theorem B.1, and pass to a further subsequence on which

\[
 Y_n=\frac{X_n-s_n}{\sqrt{V_n}}\Rightarrow\mu(dx)=f(x)\,dx,
\]

where \(f\in C^2(\mathbb R)\). Put

\[
 m_n=\frac{M_n-\mathbb EX_n}{\sqrt{V_n}},\qquad
 w_n=\frac{W_n}{V_n}.
\]

Let \(\nu_n\) be the subprobability law of \((m_n,w_n)\) restricted to
\(\mathcal A_n\).  It is supported on the fixed compact rectangle
\([-B,B]\times[\omega,C_{\mathrm D}]\).  After a further extraction,
\(\nu_n\Rightarrow\nu\), where

\[
 \nu(\mathbb R^2)\ge p_c/2.
 \tag{D.35}
\]

Let \(\lambda_n\) be the subprobability law of \(Y_n\) restricted to
\(\mathcal A_n\).  Since \(\mathbb EX_n=s_n\), its characteristic function
satisfies, by (D.30),

\[
\begin{aligned}
 \widehat\lambda_n(t)
 &=\mathbb E\left[
 \mathbf1_{\mathcal A_n}e^{\mathrm itm_n}
 \Psi_n(t\mid\mathcal G_n)\right]\\
 &=\int e^{\mathrm itm-t^2w/2}\,d\nu_n(m,w)+o(1).
\end{aligned}
\]

Weak convergence of \(\nu_n\) gives convergence of their total masses because
their supports lie in one compact rectangle. The measures \(\lambda_n\) have
the same total masses, as is also seen by putting \(t=0\) in their
characteristic functions. These masses converge to
\(\nu(\mathbb R^2)\ge p_c/2\). After dividing \(\lambda_n\) and the candidate
limit by their respective masses, the usual continuity theorem for
probability measures [Bil99] applies; multiplying the masses back gives
\(\lambda_n\Rightarrow\lambda\), where

\[
 \lambda(dx)=h(x)\,dx,
 \qquad
 h(x)=\int\frac1{\sqrt{2\pi w}}
 \exp\left(-\frac{(x-m)^2}{2w}\right)d\nu(m,w).
 \tag{D.36}
\]

The lower bound \(w\ge\omega\) and compactness of the mixing rectangle make
\(h\) continuous.  In particular,

\[
 h(0)\ge
 \frac{p_c}{2\sqrt{2\pi C_{\mathrm D}}}
 \exp\left(-\frac{B^2}{2\omega}\right)>0.
 \tag{D.37}
\]

At each finite \(n\), the full law of \(Y_n\) dominates \(\lambda_n\).  For
every nonnegative bounded continuous function \(\varphi\),

\[
 \int\varphi\,d\mu
 =\lim_n\mathbb E\varphi(Y_n)
 \ge\lim_n\int\varphi\,d\lambda_n
 =\int\varphi\,d\lambda.
\]

Hence \(\mu\ge\lambda\) as measures.  It follows that \(f\ge h\) almost
everywhere, and continuity of both densities makes the inequality
pointwise.  In particular, \(f(0)\ge h(0)>0\).

It remains to use the canonical center.  For all sufficiently large states,
Appendix C, Lemmas C.4 and C.5, give constants \(C_*,C_h,\gamma_0>0\),
depending only on the activity ceiling, such that

\[
 V_n\le C_*s_n^2,
 \qquad
 \pi_n(0)\le C_he^{-\gamma_0s_n}.
 \tag{D.38}
\]

Since \(V_n\to\infty\), these bounds imply \(s_n\to\infty\) and

\[
 \sqrt{V_n}\,\pi_n(0)
 \le\sqrt{C_*}\,C_hs_ne^{-\gamma_0s_n}\longrightarrow0.
 \tag{D.39}
\]

On the other hand, the weighted characteristic-function convergence in
Appendix B, Theorem B.1, and lattice inversion at the exact integer mean
\(s_n\) give

\[
 \sqrt{V_n}\,\pi_n(0)\longrightarrow f(0).
 \tag{D.40}
\]

Thus \(f(0)=0\), contradicting (D.37).  This proves (D.22).  \(\square\)

## D.4. Finite-branch approximation of the variance mass

Consider any canonical first-recovery sequence with \(0<z_n<27\),
\(V_n\to\infty\), and any selected componentwise rooting of each
forest. On the full rooted forest define

\[
 S_n(\alpha)=\{u\in F_n:E_n(u)\ge\alpha V_n\},
 \qquad
 R_n(\alpha)=\sum_{u\notin S_n(\alpha)}g_n(u).
 \tag{D.41}
\]

For \(0<\alpha\le1\), the set \(S_n(\alpha)\) is ancestor-closed inside
each component because (D.12) makes \(E_n\) nonincreasing along descendant
paths. A component root belongs to \(S_n(\alpha)\) exactly when its root
variance mass is at least \(\alpha V_n\); entire components of smaller mass
may be omitted.

**Lemma D.5 (finite-branch approximation).** Let
\((F_n,s_n,z_n,V_n)\) be a canonical first-recovery sequence with
\(0<z_n<27\) and \(V_n\to\infty\), choose one arbitrary root in every
component of every \(F_n\), and define \(S_n(\alpha)\) and
\(R_n(\alpha)\) by (D.41). For every
\(\varepsilon>0\) there are a fixed \(\alpha\in(0,1]\) and \(n_0\) such that

\[
 R_n(\alpha)\le\varepsilon V_n\qquad(n\ge n_0).
 \tag{D.42}
\]

For every \(n\), the rooted forest \(S_n(\alpha)\) has at most
\(1/\alpha\) rooted leaves in total and is the union of at most
\(\lceil1/\alpha\rceil\) componentwise root-to-leaf paths.

*Proof.*  Let \(O_n(\alpha)\) be the roots of the descendant components of
\(F_n\setminus S_n(\alpha)\). Thus \(O_n(\alpha)\) contains every first
vertex below the retained set and also the root of each original component
disjoint from the retained set. This is an exposed antichain, every
\(w\in O_n(\alpha)\) satisfies \(E_n(w)<\alpha V_n\), and (D.13) gives the
exact identity

\[
 R_n(\alpha)=\sum_{w\in O_n(\alpha)}E_n(w).
 \tag{D.43}
\]

Indeed, every descendant of such a \(w\) also lies outside
\(S_n(\alpha)\), because the subtree variance mass decreases along descendant
paths.
The descendant subtrees rooted at \(O_n(\alpha)\) therefore partition the
complement of \(S_n(\alpha)\).

If (D.42) failed, some \(\varepsilon_0>0\) would permit a strictly
increasing sequence \(n_j\) such that

\[
 R_{n_j}(1/j)>\varepsilon_0V_{n_j}.
\]

For \(A_j=O_{n_j}(1/j)\), one would then have

\[
 \max_{w\in A_j}\frac{E_{n_j}(w)}{V_{n_j}}<\frac1j,
 \qquad
 \frac1{V_{n_j}}\sum_{w\in A_j}E_{n_j}(w)>\varepsilon_0,
 \tag{D.44}
\]

contrary to Lemma D.4.  This proves (D.42).

If \(\mathcal L_n(\alpha)\) is the set of rooted leaves of
\(S_n(\alpha)\), then it is an antichain and each of its members has variance
mass at least \(\alpha V_n\). Therefore (D.14) gives

\[
 |\mathcal L_n(\alpha)|\alpha V_n
 \le\sum_{\ell\in\mathcal L_n(\alpha)}E_n(\ell)\le V_n.
 \tag{D.45}
\]

Every finite rooted forest is the union of its componentwise root-to-leaf
paths, proving the last assertion.  \(\square\)

The identity (D.43) is why the subtree variance mass is used only at the
exposed component roots. The interior mass \(R_n(\alpha)\) is a sum of the
nonnegative vertex variance contributions, each counted exactly once.

## D.5. Large conditional mean differences

The next estimate converts the Feller condition
\(\max_u g(u)/V\to0\) into a Lindeberg condition for the martingale array.

**Lemma D.6 (large-displacement contribution bound).** Let \(F\) be a finite rooted forest at
activity \(0<z<27\), with \(V\), \(g\), and \(\Delta\) defined by
(D.1)--(D.13). Let

\[
 g_{\max}=\max_{u\in F}g(u),\qquad
 G_S(b)=\sum_{\substack{u\in S\\|\Delta_u|>b}}g(u),
 \qquad b>1.
 \tag{D.46}
\]

If \(x=784g_{\max}/b^2<1\), then, for every \(S\subseteq F\),

\[
 G_S(b)\le
 \left(\frac{b}{b-1}\right)^2
 28x\log\left(\frac{27}{x}\right)V.
 \tag{D.47}
\]

Consequently, let \((F_n,z_n,V_n)\) be any sequence of such rooted
forest states with \(0<z_n<27\) and \(V_n\to\infty\), let
\(g_{\max,n}=\max_{u\in F_n}g_n(u)\), and suppose
\(g_{\max,n}/V_n\to0\). Then for every
\(\varepsilon>0\) and every sequence of
componentwise ancestor-closed sets \(S_n\subseteq F_n\),

\[
 \frac1{V_n}\sum_{u\in S_n}
 \mathbb E\left[(\Delta_{n,u}\eta_{n,u})^2
 \mathbf1_{\{|\Delta_{n,u}\eta_{n,u}|>
 \varepsilon\sqrt{V_n}\}}\right]\longrightarrow0.
 \tag{D.48}
\]

*Proof.*  If \(|\Delta_u|>b\), then (D.5), (D.8), and (D.9) give

\[
 p_u=\frac{g(u)}{a_uq_u\Delta_u^2}
 <\frac{784g(u)}{b^2}\le x.
 \tag{D.49}
\]

For arbitrary real numbers \(y_v\) indexed by the children of \(u\),
weighted Cauchy--Schwarz gives

\[
 \left(\sum_vp_vy_v\right)^2
 \le\left(\sum_v\frac{p_v}{q_v}\right)
 \left(\sum_vp_vq_vy_v^2\right).
 \tag{D.50}
\]

All children \(v\) of \(u\) have \(a_v=1-a_up_u\), and
\(a_up_uq_u/a_v\le p_u\).  Multiplying (D.50) by \(a_up_uq_u\) therefore
gives

\[
 a_up_uq_u\left(\sum_vp_vy_v\right)^2
 \le p_u\left(\sum_v\frac{p_v}{q_v}\right)
 \sum_va_vp_vq_vy_v^2.
 \tag{D.51}
\]

Equations (D.4)--(D.5) imply

\[
 \sum_v\frac{p_v}{q_v}
 \le28\sum_vp_v
 \le28\sum_v(-\log q_v)
 =28\log\left(\frac{zq_u}{p_u}\right)
 \le28\log\left(\frac{27}{p_u}\right).
 \tag{D.52}
\]

For a counted \(u\), (D.6) gives

\[
 \left|\sum_vp_v\Delta_v\right|=|1-\Delta_u|
 \ge\left(1-\frac1b\right)|\Delta_u|.
 \tag{D.53}
\]

Apply (D.51) with \(y_v=\Delta_v\).  Since
\(p\mapsto p\log(27/p)\) is increasing on \((0,1)\), equations
(D.49)--(D.53) yield

\[
 g(u)\le
 \left(\frac{b}{b-1}\right)^2
 28x\log\left(\frac{27}{x}\right)
 \sum_{v\in\operatorname{ch}(u)}g(v).
 \tag{D.54}
\]

Sum over the counted parents in \(S\). Each child contribution occurs on the right
at most once, and the double sum is at most \(V\) by (D.13), proving
(D.47).

Since \(|\eta_u|\le1\), the event in (D.48) implies
\(|\Delta_u|>\varepsilon\sqrt{V_n}\).  Take
\(b=\varepsilon\sqrt{V_n}\) and
\(x=784g_{\max,n}/(\varepsilon^2V_n)\). Then \(x\to0\) and
\(x\log(27/x)\to0\), while the left side of (D.48) is bounded by
\(G_{S_n}(b)/V_n\).  Equation (D.47) completes the proof.  \(\square\)

## D.6. Predictable quadratic variation on a finite-branch subtree

**Standing hypotheses for Section D.6.** Let \(F\) be a finite rooted
forest under the hard-core law at activity \(0<z<27\). Let \(S\subseteq F\)
be a finite componentwise ancestor-closed rooted subforest with \(L\) rooted
leaves in total, and let \(\mathcal R(S)\) denote its component roots. Retain
the original quantities \(p_u,\eta_u,\Delta_u,g(u)\) for \(u\in S\).
Integrating out every omitted descendant component gives an inhomogeneous
hard-core law on \(S\), with effective activities
\(0<\lambda_x\le z<27\). More precisely, if \(\mathcal O_x\) is the set of
children of \(x\) whose descendant subtrees are omitted from \(S\), and
\(\operatorname{ch}_S(x)\) denotes its retained children, then

\[
 \lambda_x=z\prod_{c\in\mathcal O_x}\frac{Q_c(z)}{P_c(z)}
 =z\prod_{c\in\mathcal O_x}q_c\le z.
\]

Indeed, an omitted child subtree contributes \(P_c(z)\) when \(x\) is absent
and \(Q_c(z)\) when \(x\) is occupied. For either orientation \(y\to x\) of
an edge, the directed-edge occupation odds in this marginal law satisfy

\[
 R_{y\to x}=\lambda_y
 \prod_{v\in N_S(y)\setminus\{x\}}(1+R_{v\to y})^{-1}<27.
 \tag{D.55}
\]

Therefore

\[
 \Pr(\xi_y=1\mid\xi_x=0)<\overline p_{27},
 \qquad
 \Pr(\xi_y=1\mid\xi_x=1)=0
 \tag{D.56}
\]

in either direction along every edge of \(S\).

The marginalization also preserves the original conditional occupation
probability at a retained vertex. Conditional on its parent being absent, the
odds at \(u\) in the marginal law are

\[
 \lambda_u\prod_{v\in\operatorname{ch}_S(u)}q_v
 =z\prod_{v\in\operatorname{ch}_F(u)}q_v
 =R_u=\frac{p_u}{q_u}.
\]

Thus

\[
 \Pr(\xi_u=1\mid\xi_{\operatorname{par}(u)}=0)=p_u.
\]

For a parent-before-child filtration on \(S\), all unrevealed descendants have
already been integrated into these odds, while the only previously revealed
neighbor of \(u\) is its parent. Let \(\mathcal F_{u^-}^S\) denote the
sigma-field generated by the retained vertices preceding \(u\). Consequently

\[
 \mathbb E(\xi_u\mid\mathcal F_{u^-}^S)
 =p_u(1-\xi_{\operatorname{par}(u)}).
\]

It follows directly that the original variable
\(\eta_u=\xi_u-p_u(1-\xi_{\operatorname{par}(u)})\) remains a martingale
difference and

\[
 \mathbb E(\eta_u^2\mid\mathcal F_{u^-}^S)
 =p_uq_u(1-\xi_{\operatorname{par}(u)}),
\]

with the virtual absent parent convention at every retained component root.
Thus the summands in
(D.57) are the predictable conditional variances of the projected
martingale from Lemma D.2.

**Lemma D.7 (quadratic-variation concentration).** Under the standing
hypotheses above, enumerate \(S\) in parent-before-child order and let
\(\mathcal F_k^S\) be the sigma-field generated by its first \(k\) occupation
variables. The predictable
quadratic variation of the projected martingale is

\[
 Q_S=\sum_{k=1}^{|S|}
 \mathbb E[(\Delta_{u_k}\eta_{u_k})^2\mid\mathcal F_{k-1}^S].
 \tag{D.57}
\]

If \(g_{\max}=\max_{u\in S}g(u)\), then

\[
 \mathbb EQ_S=\sum_{u\in S}g(u),
 \qquad
 \operatorname{Var}(Q_S)\le C_{27}L^2g_{\max}V,
 \qquad C_{27}=10\,976.
 \tag{D.58}
\]

*Proof.* If \(x\) and \(y\) lie in different components, their occupation
variables are independent and their covariance is zero. Suppose they lie in
the same component, and let \(x=v_0,v_1,\ldots,v_d=y\) be the unique path in
\(S\). For an
oriented edge \(v_jv_{j+1}\), the binary conditional expectation has the
affine form

\[
 \mathbb E(\xi_{v_{j+1}}\mid\xi_{v_j})
 =\alpha_j+\beta_j\xi_{v_j},
 \qquad
 \beta_j=\Pr(\xi_{v_{j+1}}=1\mid\xi_{v_j}=1)
          -\Pr(\xi_{v_{j+1}}=1\mid\xi_{v_j}=0).
\]

Equation (D.56) gives \(|\beta_j|<\overline p_{27}\). For \(t\in\{0,1\}\), write

\[
 m_j(t)=\mathbb E(\xi_{v_j}\mid\xi_x=t)=A_j+B_jt,
 \qquad A_0=0,\quad B_0=1.
\]

The forest Markov property and the tower rule give the two-line recursion

\[
 m_{j+1}(t)=\alpha_j+\beta_jm_j(t)
 =\bigl(\alpha_j+\beta_jA_j\bigr)+\beta_jB_jt.
\]

Thus \(B_{j+1}=\beta_jB_j\), and induction from \(B_0=1\) gives
\(B_d=\prod_{j=0}^{d-1}\beta_j\). In particular, the slope of
\(\mathbb E(\xi_y\mid\xi_x)\) as an affine function of \(\xi_x\) is this
product. Hence

\[
 \operatorname{Cov}(\xi_x,\xi_y)
 =\operatorname{Cov}(\xi_x,\mathbb E[\xi_y\mid\xi_x])
 =\operatorname{Var}(\xi_x)\prod_{j=0}^{d-1}\beta_j.
\]

Since \(\operatorname{Var}(\xi_x)\le1/4\), this proves

\[
 |\operatorname{Cov}(\xi_x,\xi_y)|
 \le\frac14\overline p_{27}^{\operatorname{dist}(x,y)}.
 \tag{D.59}
\]

A rooted forest with \(L\) rooted leaves has at most \(2L\) vertices of degree
at most one in the underlying unrooted forest; these are what we call
**unrooted leaves** here. Indeed, a nontrivial rooted component with \(l\)
rooted leaves has at most \(l+1\) unrooted leaves, while an isolated rooted
component has one;
summing over at most \(L\) components gives the claim.
For a fixed \(x\in S\), the branches beginning at vertices at a common
positive distance \(k\) from \(x\) are disjoint, and each contains an
unrooted leaf.  Hence

\[
 |\{y\in S:\operatorname{dist}(x,y)=k\}|\le 2L
 \qquad(k\ge0).
 \tag{D.60}
\]

Put

\[
 c_u=p_uq_u\Delta_u^2=\frac{g(u)}{a_u}\le28g(u).
 \tag{D.61}
\]

For a nonroot \(u=u_k\), its summand in (D.57) is
\(c_u(1-\xi_{\operatorname{par}(u)})\); every retained component-root
summand is deterministic.
Grouping by parents gives

\[
 Q_S=\sum_{r\in\mathcal R(S)}c_r
     +\sum_{x\in S}w_x(1-\xi_x),
 \qquad
 w_x=\sum_{\substack{u\in S\\\operatorname{par}(u)=x}}c_u.
 \tag{D.62}
\]

Every child branch in \(S\) contains a rooted leaf, so each vertex has at
most \(L\) children in \(S\).  Thus

\[
 \max_xw_x\le28Lg_{\max},
 \qquad
 \sum_xw_x\le28V.
 \tag{D.63}
\]

Using (D.59)--(D.60) and \((1-\overline p_{27})^{-1}=28\), we obtain

\[
\begin{aligned}
 \operatorname{Var}(Q_S)
 &\le\frac14\sum_xw_x\sum_yw_y
 \overline p_{27}^{\operatorname{dist}(x,y)}\\
 &\le\frac14(28V)(28Lg_{\max})(2L)
       \sum_{k\ge0}\overline p_{27}^k
 \le10\,976L^2g_{\max}V.
\end{aligned}
 \tag{D.64}
\]

The last numerical constant is
\(\frac14\cdot28^3\cdot2=10\,976\).

Finally,
\(\mathbb E(1-\xi_{\operatorname{par}(u)})=a_u\), so (D.61)--(D.62)
give \(\mathbb EQ_S=\sum_{u\in S}a_uc_u=\sum_{u\in S}g(u)\).
This proves (D.58).  \(\square\)

## D.7. Failure of the Feller condition

**Proposition D.8 (failure of the Feller condition).** There is no canonical
first-recovery sequence with \(0<z_n<27\), \(V_n\to\infty\), and a selected
componentwise rooting of each forest for which

\[
 g_{\max,n}:=\max_{u\in F_n}g_n(u)=o(V_n).
 \tag{D.65}
\]

*Proof.*  Assume (D.65).  For every integer \(j\ge2\), apply Lemma D.5 with
\(\varepsilon=1/j\), lower the resulting fixed threshold if necessary so
that \(\alpha_j\le1/j\), and put

\[
 \ell_j=\lceil1/\alpha_j\rceil.
\]

There is a strictly increasing sequence \(N_j\ge j\) such that, for every
\(n\ge N_j\),

\[
 \frac{R_n(\alpha_j)}{V_n}\le\frac1j,
 \qquad
 \frac{\ell_j^2g_{\max,n}}{V_n}\le\frac1j.
 \tag{D.66}
\]

For \(n\ge N_2\), let

\[
 j(n)=\max\{j:N_j\le n\},\qquad
 S_n=S_n(\alpha_{j(n)}).
\]

Then \(j(n)\to\infty\). If \(\ell_n\) is the number of rooted leaves of
\(S_n\), Lemma D.5 and (D.43) give

\[
 \sum_{u\in S_n}g_n(u)=V_n-R_n(\alpha_{j(n)})=(1-o(1))V_n,
 \qquad
 \frac{\ell_n^2g_{\max,n}}{V_n}\longrightarrow0.
 \tag{D.67}
\]

Both conclusions follow with \(j=j(n)\): one has \(n\ge N_{j(n)}\), while
Lemma D.5 gives \(\ell_n\le \ell_{j(n)}\). Thus no estimate obtained for a fixed
threshold is used before its own eventual index.

Let \(Q_n=Q_{S_n}\).  Lemma D.7 implies

\[
 \frac{\mathbb EQ_n}{V_n}\longrightarrow1,
 \qquad
 \operatorname{Var}\left(\frac{Q_n}{V_n}\right)
 \le C_{27}\frac{\ell_n^2g_{\max,n}}{V_n}\longrightarrow0.
\]

Therefore

\[
 \frac{Q_n}{V_n}\longrightarrow1
 \quad\text{in probability}.
 \tag{D.68}
\]

Write \(S_n=\{u_{n,1},\ldots,u_{n,M_n}\}\) in parent-before-child order,
let \(\mathcal F_{n,k}\) be generated by the first \(k\) listed occupation
variables, and put
\(D_{n,k}=\Delta_{n,u_{n,k}}\eta_{n,u_{n,k}}\).  For fixed
\(\varepsilon>0\), define

\[
 \Gamma_n(\varepsilon)=\frac1{V_n}\sum_{k=1}^{M_n}
 \mathbb E\left[D_{n,k}^2
 \mathbf1_{\{|D_{n,k}|>\varepsilon\sqrt{V_n}\}}
 \mid\mathcal F_{n,k-1}\right].
 \tag{D.69}
\]

Its expectation tends to zero by Lemma D.6 and (D.65).  Markov's inequality
therefore gives

\[
 \Gamma_n(\varepsilon)\longrightarrow0
 \quad\text{in probability}.
 \tag{D.70}
\]

These are finite square-integrable martingale-difference rows normalized by
\(\sqrt{V_n}\). The constant-variance martingale-array central limit theorem
stated after (B.60), applied with (D.68) and (D.70), yields

\[
 \frac{Z_{S_n}}{\sqrt{V_n}}\Rightarrow\mathcal N(0,1).
 \tag{D.71}
\]

Only the ordinary weak convergence in (D.71) is taken from the martingale
central limit theorem. No local limit theorem or adjacent-probability estimate
is attributed to Hall and Heyde; those estimates enter below from the separate
full-domain Fourier envelope.

By Lemma D.2 and (D.67),

\[
 \frac1{V_n}\mathbb E[(X_n-s_n-Z_{S_n})^2]
 =1-\frac1{V_n}\sum_{u\in S_n}g_n(u)\longrightarrow0.
 \tag{D.72}
\]

Slutsky's theorem transfers (D.71) to the original global law:

\[
 \frac{X_n-s_n}{\sqrt{V_n}}\Rightarrow\mathcal N(0,1).
 \tag{D.73}
\]

Weak convergence alone does not determine the adjacent log-concavity
difference.
For the local step, use the full-domain envelope (D.21) and set

\[
 H_{27}(u)=\exp\left\{-c_{27}\min
 (u^2,|u|^{2\alpha_{27}})\right\}.
 \tag{D.74}
\]

Every polynomial weight is integrable against \(H_{27}\).  Define

\[
 \phi_n(u)=\mathbb E\exp\left\{
 \mathrm iu\frac{X_n-s_n}{\sqrt{V_n}}\right\},
 \qquad
 I_n=[-\pi\sqrt{V_n},\pi\sqrt{V_n}],
 \qquad c_{\mathrm G}=(2\pi)^{-1/2}.
\]

Equations (D.73)--(D.74) give

\[
 \phi_n(u)\longrightarrow e^{-u^2/2},
 \qquad
 |\phi_n(u)|\le H_{27}(u)\quad(u\in I_n).
 \tag{D.75}
\]

Extend each Fourier integrand by zero outside \(I_n\).  Lattice inversion at
the exact integer center gives

\[
 \sqrt{V_n}\,\pi_n(0)
 =\frac1{2\pi}\int_{I_n}\phi_n(u)\,du
 \longrightarrow c_{\mathrm G}.
 \tag{D.76}
\]

Together with (D.39), equation (D.76) already gives a contradiction. For
completeness, the following calculation supplies a second, independent
contradiction by recovering the sign of the adjacent log-concavity
determinant.

Define

\[
 \delta_n=\pi_n(-1)+\pi_n(1)-2\pi_n(0),
 \qquad
 \tau_n=\pi_n(1)-\pi_n(-1).
 \tag{D.77}
\]

The scaled second-difference multiplier
\(2V_n(\cos(u/\sqrt{V_n})-1)\) converges to \(-u^2\) and is bounded in
absolute value by \(u^2\).  Dominated convergence with \(u^2H_{27}(u)\)
gives

\[
\begin{aligned}
 V_n^{3/2}\delta_n
 &=\frac1{2\pi}\int_{I_n}\phi_n(u)
 2V_n\left(\cos\frac{u}{\sqrt{V_n}}-1\right)du\\
 &\longrightarrow-\frac1{2\pi}
 \int_{\mathbb R}u^2e^{-u^2/2}\,du=-c_{\mathrm G}.
\end{aligned}
 \tag{D.78}
\]

Similarly, the multiplier
\(-2\mathrm i\sqrt{V_n}\sin(u/\sqrt{V_n})\) is bounded by \(2|u|\) and
converges to \(-2\mathrm iu\).  Dominated convergence and oddness give

\[
\begin{aligned}
 V_n\tau_n
 &=\frac1{2\pi}\int_{I_n}\phi_n(u)
 \left(-2\mathrm i\sqrt{V_n}\sin\frac{u}{\sqrt{V_n}}\right)du\\
 &\longrightarrow-\frac{\mathrm i}{\pi}
 \int_{\mathbb R}ue^{-u^2/2}\,du=0.
\end{aligned}
 \tag{D.79}
\]

The exact relations

\[
 \pi_n(-1)=\pi_n(0)+\frac{\delta_n-\tau_n}{2},
 \qquad
 \pi_n(1)=\pi_n(0)+\frac{\delta_n+\tau_n}{2}
\]

imply

\[
 \pi_n(0)^2-\pi_n(-1)\pi_n(1)
 =-\pi_n(0)\delta_n-\frac{\delta_n^2-\tau_n^2}{4}.
 \tag{D.80}
\]

By (D.76), (D.78), and (D.79),

\[
 V_n^2\bigl[\pi_n(0)^2-\pi_n(-1)\pi_n(1)\bigr]
 \longrightarrow c_{\mathrm G}^2=\frac1{2\pi}>0.
 \tag{D.81}
\]

This contradicts the canonical first-recovery sign (D.2), and proves the
proposition.  \(\square\)

## D.8. Uniformization over all rootings

*Proof of Theorem D.1.*  If the asserted constants did not exist, then for
every integer \(j\ge1\) one could choose a canonical first-recovery state
with \(0<z_j<27\), \(V_j\ge j\), and a choice of one root in each
component of \(F_j\) such that

\[
 \max_{u\in F_j}\frac{g_j(u)}{V_j}<\frac1j.
\]

These choices would form a sequence forbidden by Proposition D.8.  Hence
uniform constants \(\kappa_{27}>0\) and \(V_{27}<\infty\) exist.  Since the
contrary sequence was allowed to select arbitrary componentwise rootings in
every state, the conclusion holds for every such rooting. The resulting
vertex belongs to the original forest, with the weight induced
by that rooting.  \(\square\)


# References

[AMSE87] Y. Alavi, P. J. Malde, A. J. Schwenk, and P. Erdős,
*The vertex independence sequence of a graph is not constrained*, Congressus
Numerantium **58** (1987), 15--23.

[BES18] P. Bahls, B. Ethridge, and L. Szabó, *Unimodality of the independence
polynomials of non-regular caterpillars*, Australasian Journal of
Combinatorics **71** (2018), 104--112.

[BG21] A. Basit and D. Galvin, *On the independent set sequence of a tree*,
Electronic Journal of Combinatorics **28** (2021), Paper P3.23.
DOI: 10.37236/9896.

[BGG26] C. Bautista-Ramos, C. Guillén-Galván, and P. Gómez-Salgado,
*Linear recurrences for non-log-concave independence polynomials of trees*,
arXiv:2603.14204, 2026.

[Bil99] P. Billingsley, *Convergence of Probability Measures*, second edition,
Wiley, 1999.

[CS07] M. Chudnovsky and P. Seymour, *The roots of the independence polynomial
of a clawfree graph*, Journal of Combinatorial Theory, Series B **97** (2007),
350--357. DOI: 10.1016/j.jctb.2006.06.001.

[DK25] E. Davies and R. J. Kang, *The hard-core model in graph theory*,
arXiv:2501.03379, 2025.

[DST25] E. Davies, J. S. Sandhu, and B. Tan, *On expectations and variances in
the hard-core model on bounded degree graphs*, arXiv:2505.13396, 2025.

[Fel71] W. Feller, *An Introduction to Probability Theory and Its
Applications*, volume II, second edition, Wiley, 1971.

[Gal26] D. Galvin, *Trees with non log-concave independent set sequences*,
arXiv:2502.10654, revised 2026.

[GH83] I. Gutman and F. Harary, *Generalizations of the matching polynomial*,
Utilitas Mathematica **24** (1983), 97--106.

[GH18] D. Galvin and J. Hilyard, *The independent set sequence of some
families of trees*, Australasian Journal of Combinatorics **70** (2018),
236--252.

[HH80] P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*,
Academic Press, 1980.

[Ham90] Y. O. Hamidoune, *On the numbers of independent k-sets in a claw-free
graph*, Journal of Combinatorial Theory, Series B **50** (1990), 241--244.
DOI: 10.1016/0095-8956(90)90079-F.

[Hei25] S. Heilman, *Independent sets of random trees and sparse random
graphs*, Journal of Graph Theory **109** (2025), 294--309.
DOI: 10.1002/jgt.23225.

[HKV26] T. Hibi, S. Kara, and D. Vien, *Symmetric and unimodal independence
polynomials of trees*, arXiv:2604.18824, 2026.

[Hoe63] W. Hoeffding, *Probability inequalities for sums of bounded random
variables*, Journal of the American Statistical Association **58** (1963),
13--30. DOI: 10.1080/01621459.1963.10500830.

[JPSS22] V. Jain, W. Perkins, A. Sah, and M. Sawhney, *Approximate counting
and sampling via local central limit theorems*, in *Proceedings of the 54th
Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 1473--1486.
DOI: 10.1145/3519935.3519957.

[KL23] O. Kadrawi and V. E. Levit, *The independence polynomial of trees is
not always log-concave starting from order 26*, Ars Mathematica Contemporanea
**25** (2025), Paper P4.03. DOI: 10.26493/1855-3974.3207.2ad.

[Li26] G. M. X. Li, *Unimodality of independence polynomials of two family of
trees*, arXiv:2603.03025, 2026.

[LLYZ25] E. Y. H. Li, G. M. X. Li, A. L. B. Yang, and Z.-X. Zhang,
*A symmetric function approach to log-concavity of independence polynomials*,
arXiv:2501.04245, 2025.

[LM03] V. E. Levit and E. Mandrescu, *On unimodality of independence
polynomials of some well-covered trees*, in *Discrete Mathematics and
Theoretical Computer Science*, Lecture Notes in Computer Science **2731**,
Springer, 2003, 237--256. DOI: 10.1007/3-540-45066-1_19.

[LM05] V. E. Levit and E. Mandrescu, *The independence polynomial of a graph:
a survey*, in *Proceedings of the First International Conference on Algebraic
Informatics*, Aristotle University of Thessaloniki, 2005, 233--254.

[LM06] V. E. Levit and E. Mandrescu, *Partial unimodality for independence
polynomials of König--Egerváry graphs*, Congressus Numerantium **179** (2006),
109--119.

[LP86] L. Lovász and M. D. Plummer, *Matching Theory*, North-Holland
Mathematics Studies **121**, North-Holland, 1986.

[RS25] E. Ramos and S. Sun, *An AI enhanced approach to the tree unimodality
conjecture*, arXiv:2510.18826, 2025.

[SS05] A. D. Scott and A. D. Sokal, *The repulsive lattice gas, the
independent-set polynomial, and the Lovász local lemma*, Journal of Statistical
Physics **118** (2005), 1151--1261. DOI: 10.1007/s10955-004-2055-4.

[Wei06] D. Weitz, *Counting independent sets up to the tree threshold*, in
*Proceedings of the 38th Annual ACM Symposium on Theory of Computing
(STOC 2006)*, 140--149. DOI: 10.1145/1132516.1132538.

[YMK21] R. Yosef, M. Mizrachi, and O. Kadrawi, *On unimodality of independence
polynomials of trees*, arXiv:2101.06744, 2021, revised 2022.

[ZC19] B.-X. Zhu and Y. Chen, *Log-concavity of independence polynomials of
some kinds of trees*, Applied Mathematics and Computation **342** (2019),
35--44. DOI: 10.1016/j.amc.2018.09.028.

[ZX26] W. Zhang and K. Xu, *On the variance fraction of the hard-core model on
graphs with bounded maximum degree*, arXiv:2604.01717, 2026.
