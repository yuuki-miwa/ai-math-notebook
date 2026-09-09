# A seven-prime obstruction for distinct odd covering systems

**Yuuki Miwa**  
**Working draft v3 — 4 September 2026**

> **Status.** This draft records a computer-assisted theorem candidate. The analytic reduction and exact finite certificate have been internally audited, and the finite functional has now been reproduced by two independently structured implementations in addition to the primary code. The argument has not yet received specialist external review. The theorem is therefore stated in mathematical form below while the draft itself should not yet be cited as a finished result.

## Abstract

A covering system is a finite family of residue classes whose union is the set of integers. The Erdős–Selfridge problem asks whether a covering system can have all moduli odd, distinct, and greater than one. Berger, Felzenbaum and Fraenkel proved classically that the least common multiple of any hypothetical system has at least six distinct prime divisors. We give an exact computer-assisted obstruction improving this unrestricted lower bound from six to seven. No bound on the least common multiple, and no bound on any prime-power exponent, is imposed.

The proof first completes the set of moduli to all nontrivial divisors of \(N\), removes the pure prime-power classes, and works on the resulting Chinese-remainder product. The prime \(3\) is used as a pivot. Its survivor coordinate is resolved to depth three as a rooted tree of eighteen possible residue leaves modulo \(27\). Selected two-prime axis families are incorporated into an exact hierarchical skeleton, while every remaining mixed class is clipped by the complement of that skeleton on coordinates outside its own support. Separate convexity reduces all continuous allocation variables to finitely many simplex vertices, and a promotion lemma permits refinement only of the states not already certified at the shallow level.

For the extremal support \(\{3,5,7,11,13,17\}\), the certificate consists of 28 rooted-tree orbits of the \(3\)-adic profile, \(21^5\) shallow axis states per orbit, and \(19^3\) refinements of only 2505 critical shallow states. Every comparison is an integer comparison with common denominator \(601425\). The final maximum is

\[
\frac{200282}{200475}=0.9990372864\ldots<1,
\]

with exact gap \(193/200475\). Two independently structured reconstructions reproduce the orbit data and the exact maxima; one of them evaluates the displayed formulas with all eighteen leaves carried explicitly and without the primary subset-product compression.

---

## 1. Introduction

A **covering system** is a finite family

\[
\mathcal C=\{a_i\pmod{m_i}:1\le i\le k\}
\]

such that every integer belongs to at least one of the displayed residue classes. The system is **distinct** if the moduli \(m_i\) are pairwise distinct. The Erdős–Selfridge odd covering problem asks whether there exists a distinct covering system in which every modulus is odd and greater than one.

The problem remains open [MS26, BCHLPSW26]. For the unrestricted prime-power setting, Berger, Felzenbaum and Fraenkel first proved the necessary condition

\[
\prod_{i=1}^n\frac{p_i-1}{p_i-2}
-
\sum_{i=1}^n\frac1{p_i-2}>2,
\]

where \(p_1<\cdots<p_n\) are the distinct prime divisors of the least common multiple [BFF86]. This implies \(n\ge5\). Their strengthened condition then excluded the extremal five-prime case \(\{3,5,7,11,13\}\), proving the classical unrestricted bound \(n\ge6\) [BFF87]. The result below advances this bound by one.

Hough and Nielsen proved that every distinct covering system contains a modulus divisible by either \(2\) or \(3\) [HN19]. Consequently, the least common multiple of a hypothetical odd distinct covering is divisible by \(3\). Further unrestricted structure is known: in the odd case, one has a modulus divisible by \(9\), or else one modulus divisible by \(3\) and another divisible by \(5\) [BBMST22]. In the square-free setting, Guo and Sun obtained a strong lower bound [GS05], and the square-free odd case was later ruled out completely [BBMST21]. Arbitrary prime powers remain the principal difficulty.

The purpose of this paper is to establish the following finite-support obstruction.

### Theorem 1.1 — Seven-prime obstruction

Let \(\mathcal C=\{a_i\pmod{m_i}\}\) be a covering system with pairwise distinct odd moduli \(m_i>1\), and let

\[
N=\operatorname{lcm}(m_1,\ldots,m_k).
\]

Then

\[
\boxed{\omega(N)\ge7},
\]

where \(\omega(N)\) denotes the number of distinct prime divisors of \(N\).

The proof is computer-assisted only in a finite maximization stated precisely in Proposition 9.1. All reductions before that proposition are uniform in the prime-power exponents. In particular, the computation does not enumerate integers \(N\), does not impose an LCM cutoff, and does not truncate the exponents. Relative to [BFF87], Theorem 1.1 excludes the remaining six-prime possibility and raises the known unrestricted support lower bound from six to seven.

### 1.1. Structure of the proof

The argument has four main ingredients.

1. **Pure-tower preprocessing.** For each prime dividing \(N\), remove the classes whose moduli are pure powers of that prime. Their common complement is an exact CRT product, and every remaining prime-power slice has an exponent-free total capacity bounded by \(1/(p-2)\).

2. **A hierarchical \(3\)-adic skeleton.** Since \(3\mid N\), resolve the survivor of the \(3\)-coordinate to depth three. Selected families \(3^g p^f\) are incorporated exactly along this tree.

3. **Clipped residual bounds.** A mixed class with non-\(3\) support \(T\) is clipped by the exact skeleton complement on every prime coordinate outside \(T\). This captures correlations that a global union bound discards.

4. **Finite convexity certificate.** The resulting functional is separately convex in the \(3\)-adic profile and in every axis-allocation simplex. Its maximum therefore occurs at a product of vertices. A shallow scan leaves only 2505 critical states, all of which close after a selective depth-three promotion.

The common denominator in the final computation is small enough that all proof-relevant arithmetic is integral.

---

## 2. Completion and periodic reduction

Let \(N=\operatorname{lcm}(m_i)\). Every class in \(\mathcal C\) is periodic modulo \(N\), so \(\mathcal C\) covers \(\mathbb Z\) if and only if its images cover \(\mathbb Z/N\mathbb Z\).

### Lemma 2.1 — Divisor completion

Suppose a distinct covering system has LCM \(N\). For each divisor \(d\mid N\), \(d>1\), not already used as a modulus, adjoin one arbitrary residue class modulo \(d\). The resulting family remains a distinct covering system.

Hence it is enough to rule out the following larger relaxation:

> one residue class is available for every nontrivial divisor of \(N\).

#### Proof

Adjoining classes cannot destroy coverage. Since each previously unused divisor is added at most once, the moduli remain distinct. ∎

The same observation permits **exponent padding**. If a later argument requires a larger exponent of a prime already dividing \(N\), enlarge \(N\) by that prime power. The original covering still consists of classes modulo divisors of the enlarged integer, and divisor completion only enlarges the family. We shall therefore assume that the exponent of \(3\) in \(N\) is at least three. This is the only input needed later to resolve the \(3\)-coordinate modulo \(27\).

---

## 3. Removing the pure prime-power towers

Write

\[
N=\prod_{p\mid N}p^{e_p}.
\]

For every prime \(p\mid N\), divisor completion supplies one class modulo each of

\[
p,p^2,\ldots,p^{e_p}.
\]

Let \(S_p\subseteq\mathbb Z/p^{e_p}\mathbb Z\) be the complement of these pure classes.

### Lemma 3.1 — Pure-tower survivor size

Define

\[
u_{p,e}:=\frac{(p-2)p^e+1}{p-1}.
\]

Then

\[
|S_p|\ge u_{p,e_p}.
\]

Moreover, the normalized mass in \(S_p\) of any fixed residue class modulo \(p^f\) is at most

\[
c_{p,e_p}(f):=\frac{p^{e_p-f}}{u_{p,e_p}},
\]

and

\[
 b_p(e_p):=\sum_{f=1}^{e_p}c_{p,e_p}(f)
 =\frac{p^{e_p}-1}{(p-2)p^{e_p}+1}
 <\frac1{p-2}.
\]

#### Proof

A class modulo \(p^f\) contains \(p^{e_p-f}\) points modulo \(p^{e_p}\). The union bound gives

\[
|S_p|\ge p^{e_p}-\sum_{f=1}^{e_p}p^{e_p-f}
=p^{e_p}-\frac{p^{e_p}-1}{p-1}
=u_{p,e_p}.
\]

The slice bound follows by dividing \(p^{e_p-f}\) by this lower bound. Summing the resulting geometric series gives the displayed formula for \(b_p(e_p)\), and the final strict inequality is immediate. ∎

Set

\[
\beta_p:=\frac1{p-2}.
\]

Replacing each finite \(b_p(e_p)\) by \(\beta_p\) enlarges the feasible relaxation and removes all exponent dependence.

### Lemma 3.2 — Exact product survivor

After removing all pure prime-power classes, the common survivor is exactly

\[
S=\prod_{p\mid N}S_p
\]

under the Chinese remainder identification

\[
\mathbb Z/N\mathbb Z\cong\prod_{p\mid N}\mathbb Z/p^{e_p}\mathbb Z.
\]

#### Proof

Every pure class depends on one prime coordinate only. Avoiding all pure classes is therefore equivalent to belonging to \(S_p\) in every coordinate. ∎

All measures below are normalized on this product space.

---

## 4. The \(3\)-adic profile

By [HN19], an odd distinct covering must have \(3\mid N\). The pure class modulo \(3\) removes one complete mod-\(3\) branch. Relabel the two remaining branches as the live branches.

At depth three there are eighteen possible leaves modulo \(27\) under those two branches. Let \(\tau_a\) be the normalized \(S_3\)-mass of leaf \(a\), where \(1\le a\le18\).

### Lemma 4.1 — Profile polytope

The actual profile belongs to the compact polytope

\[
K_3=\left\{\tau\in\mathbb R^{18}:
0\le\tau_a\le\frac2{27},\quad
\sum_{a=1}^{18}\tau_a=1
\right\}.
\]

#### Proof

By exponent padding in Section 2, \(e_3\ge3\). A mod-\(27\) leaf contains at most \(3^{e_3-3}\) points modulo \(3^{e_3}\). Lemma 3.1 gives

\[
|S_3|\ge\frac{3^{e_3}+1}{2},
\]

so one leaf has normalized mass strictly less than \(2/27\). Passing to the closed upper bound only enlarges the feasible set. ∎

### Lemma 4.2 — Vertices of \(K_3\)

At every vertex of \(K_3\), the scaled profile \(w_a=27\tau_a\) has

- thirteen entries equal to \(2\),
- one entry equal to \(1\), and
- four entries equal to \(0\).

Consequently there are

\[
18\binom{17}{4}=42840
\]

labelled vertices.

#### Proof

The polytope is the intersection of the hyperplane \(\sum\tau_a=1\) with the box \([0,2/27]^{18}\). At a vertex, all but at most one coordinate are box endpoints. Since the scaled coordinates sum to \(27\), the displayed multiset is forced. ∎

The rooted tree has two live mod-\(3\) branches, each containing three mod-\(9\) nodes, each of which contains three mod-\(27\) leaves. Permuting siblings at any node preserves every functional introduced below. Canonicalizing the 42,840 labelled vertices under these rooted-tree automorphisms gives exactly 28 orbits. The orbit enumeration is independently regenerated by `src/tau3_orbit_audit.py`.

### Remark 4.3 — Actual pure-tower profiles inside the relaxation

The polytope \(K_3\) is deliberately larger than the set of profiles produced by three nested-or-disjoint pure residue classes. Let \(L\) be the number of depth-three leaves left alive after the pure classes modulo \(3,9,27\). The mod-\(9\) class removes either no new live leaf or one complete three-leaf node, and the mod-\(27\) class removes either no new live leaf or one further leaf. Hence

\[
L\in\{14,15,17,18\}.
\]

The deeper pure classes remove in total at most

\[
\sum_{j=4}^{e_3}3^{e_3-j}
=\frac{3^{e_3-3}-1}{2}
\]

points, so

\[
|S_3|>3^{e_3-3}\left(L-\frac12\right),
\qquad
\tau_a<\frac{2}{2L-1}.
\]

Thus the universal bound \(2/27\) is attained only in the limiting \(L=14\) regime. At a vertex of the larger polytope \(K_3\), closure-realizability requires the four zero leaves to consist of one complete mod-\(9\) node and one additional leaf. Among the three Stage-I critical orbit types, types 7 and 13 have this form, whereas type 11 does not. In particular, the global Stage-II maximum is also attained at type 13, so the final extremum is not supported only by an impossible profile of the enlarged polytope. The script `scripts/k3_actual_profile_audit.py` records this check.

---

## 5. Axis skeletons

For the extremal six-prime template, let

\[
P=\{5,7,11,13,17\}.
\]

For \(p\in P\) and a \(3\)-adic level \(g\ge1\), consider the family of axis moduli

\[
3^g p^f,\qquad 1\le f\le e_p.
\]

At each level, group these classes by their \(3\)-adic node. In the \(p\)-coordinate, take the union of the corresponding slices, then remove the part already exposed by axis families at ancestor nodes. Let

\[
x^{(g)}_{p,v}
\]

be the resulting new normalized \(p\)-mass exposed at node \(v\).

### Lemma 5.1 — Level-wise axis budget

For every fixed \(p\) and \(g\),

\[
x^{(g)}_{p,v}\ge0,
\qquad
\sum_vx^{(g)}_{p,v}\le b_p(e_p)<\beta_p.
\]

#### Proof

At a fixed level \(g\), each exponent \(f\) contributes one axis class and hence one \(p^f\)-slice to one node. Before disjointization, the sum over node-union masses is at most the sum of the individual slice capacities. Lemma 3.1 bounds this by \(b_p(e_p)\). Removing ancestor mass can only decrease the total. The same budget may be used separately at different values of \(g\), because the moduli \(3^gp^f\) are distinct as \(g\) varies and divisor completion supplies one class for each such divisor. ∎

For a depth-three leaf \(a\), define

\[
q_{p,a}:=1-\sum_{g\le3}x^{(g)}_{p,\operatorname{anc}_g(a)},
\]

where the sum includes only the levels promoted into the exact skeleton. Thus \(q_{p,a}\) is the fraction of the \(p\)-coordinate not covered by the exposed \(p\)-axis union along the path to \(a\). These factors are nonnegative throughout the relaxation: Stage I subtracts at most \(2\beta_p\), while Stage II subtracts at most \(3\beta_p\); the worst case is \(p=5\), where \(1-3\beta_5=0\).

### Lemma 5.2 — Exact skeleton complement

Conditional on the \(3\)-adic leaf \(a\), the fraction of the non-\(3\) coordinates avoiding every exposed axis family is

\[
\prod_{p\in P}q_{p,a}.
\]

Hence the total mass covered by the axis skeleton is

\[
U_{\mathrm{skel}}
=\sum_a\tau_a\left(1-\prod_{p\in P}q_{p,a}\right).
\]

#### Proof

For fixed \(a\), the exposed axis union associated with a prime \(p\) is a measurable subset of the \(p\)-coordinate with complement mass \(q_{p,a}\). Distinct primes are independent coordinates in the CRT product \(S\), so the simultaneous complement is their product. ∎

This exact product, rather than a union bound over all axis classes, is the principal source of savings.

---

## 6. Residual mixed classes and the clipped functional

For a residual modulus, let \(T\subseteq P\) be its non-\(3\) prime support. Summing over every positive exponent on the primes of \(T\) gives the uniform capacity bound

\[
B_T:=\prod_{p\in T}\beta_p.
\]

Indeed, the sum over exponent vectors factorizes as

\[
\sum_{(f_p)_{p\in T}}\prod_{p\in T}c_{p,e_p}(f_p)
=\prod_{p\in T}b_p(e_p)
\le B_T.
\]

Only skeleton coordinates outside \(T\) are used for clipping. Define

\[
R_{T,a}:=\prod_{p\in P\setminus T}q_{p,a}.
\]

Let \(\mathcal B_1\) denote the two live mod-\(3\) branches and \(\mathcal B_2\) the six live mod-\(9\) nodes. For a fixed \(T\), put

\[
L_0(T)=\sum_a\tau_aR_{T,a},
\]

\[
L_1(T)=\max_{V\in\mathcal B_1}\sum_{a\subset V}\tau_aR_{T,a},
\]

\[
L_2(T)=\max_{V\in\mathcal B_2}\sum_{a\subset V}\tau_aR_{T,a},
\]

\[
L_3(T)=\max_a\tau_aR_{T,a},
\qquad
H(T)=\max_aR_{T,a}.
\]

### Lemma 6.1 — Residual family bounds

For a fixed nonempty support \(T\):

- at \(3\)-adic exponent \(g=0\), the residual contribution is at most \(B_TL_0(T)\), and this case occurs only when \(|T|\ge2\);
- at \(g=1\), the residual contribution is at most \(B_TL_1(T)\);
- at \(g=2\), it is at most \(B_TL_2(T)\);
- at \(g=3\), it is at most \(B_TL_3(T)\);
- the total contribution of all \(g\ge4\) is at most
  \[
  \frac{B_T}{27}H(T).
  \]

At levels already promoted for singleton \(T\), the corresponding singleton residual term is omitted.

#### Proof

Fix an exponent vector on \(T\). Its non-\(3\) slice has normalized capacity at most \(\prod_{p\in T}c_{p,e_p}(f_p)\). On a \(3\)-adic region, the skeleton complement on coordinates outside \(T\) has mass \(R_{T,a}\). The residue modulo \(3^g\) can occupy at most the whole live space when \(g=0\), one live branch when \(g=1\), one live mod-\(9\) node when \(g=2\), and one leaf when \(g=3\). Maximizing over those placements gives \(L_0,L_1,L_2,L_3\), respectively. Summing over exponent vectors gives the factor \(B_T\).

For \(g\ge4\), Lemma 3.1 gives

\[
\sum_{g=4}^{e_3}c_{3,e_3}(g)
<\sum_{g=4}^{\infty}\frac{2}{3^g}
=\frac1{27}.
\]

A deeper residue lies inside one mod-\(27\) leaf, so clipping outside \(T\) contributes at most \(H(T)\). Summing over \(g\) and exponent vectors gives the tail bound. ∎

The maximum in \(H(T)\) is deliberately taken over all eighteen leaves, including leaves of zero \(\tau\)-mass. This slightly weaker form is essential for the convexity argument in the next section.

### 6.1. Stage-I functional

At Stage I, all singleton axis families at levels \(g=1,2\) are promoted, while every singleton at \(g=3\) remains residual. The upper bound is

\[
\begin{aligned}
F_2(\tau,x)
={}&U_{\mathrm{skel}}
+\sum_{\substack{\varnothing\ne T\subseteq P\\|T|\ge2}}
B_T\bigl(L_0(T)+L_1(T)+L_2(T)\bigr)\\
&+\sum_{\varnothing\ne T\subseteq P}B_TL_3(T)
+\sum_{\varnothing\ne T\subseteq P}\frac{B_T}{27}H(T).
\end{aligned}
\tag{6.1}
\]

### 6.2. Stage-II functional

At Stage II, the singleton level-three families are additionally promoted for

\[
P_0=\{5,7,11\}.
\]

The corresponding upper bound is

\[
\begin{aligned}
F_3(\tau,x)
={}&U_{\mathrm{skel}}
+\sum_{\substack{\varnothing\ne T\subseteq P\\|T|\ge2}}
B_T\bigl(L_0(T)+L_1(T)+L_2(T)+L_3(T)\bigr)\\
&+B_{\{13\}}L_3(\{13\})+B_{\{17\}}L_3(\{17\})
+\sum_{\varnothing\ne T\subseteq P}\frac{B_T}{27}H(T).
\end{aligned}
\tag{6.2}
\]

By Lemmas 5.2 and 6.1, these are valid upper bounds for the fraction of the pure-tower survivor covered by all remaining divisor classes.

---

## 7. Convexity, symmetry, and adaptive promotion

For fixed \(p\) and \(g\), the relaxed variables \(x^{(g)}_{p,v}\) range over the simplex

\[
\Delta_{p,g}=\left\{x_v\ge0:\sum_vx_v\le\beta_p\right\}.
\]

Its vertices are the zero vector and the vectors placing the full budget \(\beta_p\) on one node.

### Lemma 7.1 — Separate convexity

Both \(F_2\) and \(F_3\) are convex in \(\tau\in K_3\) when all axis blocks are fixed, and convex in each simplex block \(x^{(g)}_{p,\cdot}\) when every other variable is fixed.

#### Proof

Fix one axis block. For each leaf, \(q_{p,a}\) is affine in that block. The skeleton term is affine because only one factor in \(\prod_pq_{p,a}\) varies. Every residual quantity is either affine or the maximum of finitely many affine functions. The corrected tail \(H(T)=\max_aR_{T,a}\) has the same form. Thus the full functional is convex in the block.

For fixed axis data, \(U_{\mathrm{skel}}\) and \(L_0\) are affine in \(\tau\); \(L_1,L_2,L_3\) are maxima of linear forms; and \(H\) is independent of \(\tau\). Hence the functional is convex in \(\tau\). ∎

### Corollary 7.2 — Vertex reduction

A maximum of \(F_2\) or \(F_3\) on the product of \(K_3\) and the axis simplices occurs at a product of vertices.

#### Proof

A convex function on a compact polytope has a maximizing vertex. Replace one block at a time by a maximizing vertex while fixing all other blocks. ∎

At levels one and two, each non-\(3\) prime therefore has

\[
(1+2)(1+6)=21
\]

possible shallow states. A promoted level-three block has \(1+18=19\) possibilities.

### Lemma 7.3 — Rooted-tree symmetry

The functionals are invariant under swapping the two live mod-\(3\) branches, independently permuting the three mod-\(9\) children of either branch, and independently permuting the three mod-\(27\) leaves under any mod-\(9\) node, provided the axis choices are relabelled by the same automorphism.

Consequently one representative from each of the 28 orbits of \(K_3\)-vertices suffices.

#### Proof

Every term in (6.1) and (6.2) is expressed through sums or maxima over complete rooted-tree levels. A rooted-tree automorphism merely permutes the indexing sets of those sums and maxima. ∎

### Lemma 7.4 — Promotion

Suppose the singleton family with non-\(3\) support \(\{p\}\) at level \(g=3\) is currently bounded by the residual term \(B_{\{p\}}L_3(\{p\})\). Incorporating that family into the exact skeleton and recomputing all later clipped terms cannot increase the total upper bound.

#### Proof

Write \(y_a\ge0\) for the newly exposed \(p\)-coordinate mass assigned to leaf \(a\). The level-wise budget gives

\[
\sum_a y_a\le\beta_p=B_{\{p\}}.
\]

Before promotion, let \(q_{p,a}\) denote the \(p\)-coordinate complement and put

\[
R_{\{p\},a}=\prod_{r\in P\setminus\{p\}}q_{r,a}.
\]

After promotion, \(q_{p,a}\) is replaced by \(q_{p,a}-y_a\). Hence the increase in the exact skeleton term is exactly

\[
\sum_a\tau_a y_aR_{\{p\},a}
\le
\left(\sum_a y_a\right)
\max_a\tau_aR_{\{p\},a}
\le
B_{\{p\}}L_3(\{p\}),
\]

which is precisely the old residual allowance for the promoted singleton family.

Now consider any other residual support \(T\). If \(p\in T\), then \(R_{T,a}\) does not involve \(q_{p,a}\), so all of its clipped terms are unchanged. If \(p\notin T\), then \(R_{T,a}\) decreases pointwise, so each of \(L_0(T),L_1(T),L_2(T),L_3(T)\) and \(H(T)\) can only decrease. The promoted singleton residual term is removed. Thus the new total upper bound is no larger than the old one. ∎

Consequently, take any product vertex of the full Stage-II relaxation and forget its three level-three promotion blocks. If the resulting shallow vertex has \(F_2<1\), Lemma 7.4 gives \(F_3\le F_2<1\). Therefore only the shallow product vertices with \(F_2\ge1\) require explicit Stage-II enumeration.

---

## 8. Reduction to the extremal six-prime support

For a five-tuple of nonnegative budgets \(\boldsymbol\beta=(\beta_1,\ldots,\beta_5)\), let \(\mathcal M(\boldsymbol\beta)\) be the supremum of the corrected relaxation, with the first three coordinates selectively promoted at level three.

### Lemma 8.1 — Budget monotonicity

If \(\boldsymbol\beta\le\boldsymbol\beta'\) coordinatewise, then

\[
\mathcal M(\boldsymbol\beta)\le\mathcal M(\boldsymbol\beta').
\]

#### Proof

Increasing a budget enlarges every axis simplex. At a fixed feasible point from the smaller domain, the skeleton term is unchanged, while every residual coefficient

\[
B_T=\prod_{i\in T}\beta_i
\]

is nonnegative and coordinatewise nondecreasing. Thus the value at every old feasible point cannot decrease, and taking suprema proves the claim. ∎

Let the non-\(3\) prime divisors of \(N\) be

\[
q_1<\cdots<q_m,\qquad m\le5.
\]

Pad to five coordinates with zero budgets. Since the \(i\)-th prime after \(3\) is at least \(5,7,11,13,17\), respectively,

\[
\left(\frac1{q_1-2},\ldots,\frac1{q_m-2},0,\ldots,0\right)
\le
\left(\frac13,\frac15,\frac19,\frac1{11},\frac1{15}\right).
\]

A zero-budget coordinate contributes no skeleton mass and annihilates every residual support containing it. Hence Lemma 8.1 reduces every support of at most six primes to

\[
\{3,5,7,11,13,17\}.
\]

---

## 9. The exact finite certificate

For the five non-\(3\) primes, write

\[
(\beta_5,\beta_7,\beta_{11},\beta_{13},\beta_{17})
=\left(\frac13,\frac15,\frac19,\frac1{11},\frac1{15}\right).
\]

Set

\[
(d_1,d_2,d_3,d_4,d_5)=(3,5,9,11,15),
\qquad
D=\prod_{i=1}^5d_i=22275.
\]

At a profile vertex, \(w_a=27\tau_a\in\{0,1,2\}\). At an axis-simplex vertex, each factor \(q_{i,a}\) has the form

\[
q_{i,a}=\frac{Q_{i,a}}{d_i},
\]

where \(Q_{i,a}\) is an integer obtained from \(d_i\) by subtracting one for each selected ancestor node on the path to \(a\). Therefore

\[
B_TR_{T,a}
=\frac{\prod_{i\notin T}Q_{i,a}}{D},
\]

and every term in \(F_2,F_3\) has common denominator

\[
27D=601425.
\]

The scanners therefore compare integer numerators only. The machine-assisted assertion below is therefore a finite statement about the explicit functions in (6.1) and (6.2), not an appeal to floating-point optimization or to an opaque search oracle. A line-by-line formula-to-code specification is supplied separately in `paper/certificate_specification_v2.md`.

### Proposition 9.1 — Computational certificate

For every vertex of the corrected relaxation associated with the support \(\{3,5,7,11,13,17\}\), the total covered fraction is at most

\[
\frac{600846}{601425}
=\frac{200282}{200475}<1.
\]

#### Certificate protocol

1. Generate the 42,840 labelled vertices of \(K_3\) and reduce them to 28 rooted-tree orbits.
2. For each orbit, enumerate all
   \[
   21^5=4,084,101
   \]
   Stage-I axis states.
3. Retain only the states whose numerator is at least \(601425\). Exactly three orbit types survive, with counts
   \[
   30,\qquad1161,\qquad1314,
   \]
   for a total of \(2505\).
4. For every surviving state, enumerate the \(19^3=6859\) level-three promotion choices for the primes \(5,7,11\).
5. Take the largest Stage-II numerator.

The exact Stage-I data relevant to refinement are

| profile type | Stage-I maximum | critical states |
|---:|---:|---:|
| 7 | \(601693/601425\) | 30 |
| 11 | \(605556/601425\) | 1161 |
| 13 | \(605556/601425\) | 1314 |

Every other profile type is already below one. The closest excluded type is type 6, with

\[
\frac{601190}{601425}=0.9996092613\ldots.
\]

The Stage-II maxima are

| profile type | evaluations | Stage-II maximum |
|---:|---:|---:|
| 7 | 205,770 | \(597601/601425\) |
| 11 | 7,963,299 | \(600846/601425\) |
| 13 | 9,012,726 | \(600846/601425\) |

Thus the global maximum is

\[
M_6=\frac{600846}{601425}
=\frac{200282}{200475},
\]

and

\[
1-M_6=\frac{579}{601425}
=\frac{193}{200475}.
\]

The full 28-row Stage-I table is given in Appendix A. The machine-readable expected values are in `expected/certificate_manifest.json`.

### 9.1. A worst-state decomposition

One worst witness occurs for profile type 11, Stage-I states

\[
(18,8,12,13,12)
\]

and level-three choices

\[
(9,0,3)
\]

for the primes \((5,7,11)\). In units of the common denominator, its score decomposes as

| component | numerator |
|---|---:|
| exact skeleton | 326085 |
| residual \(g=0\) | 120474 |
| residual \(g=1\) | 84966 |
| residual \(g=2\) | 33300 |
| residual \(g=3\) | 15660 |
| tail \(g\ge4\) | 20361 |
| **total** | **600846** |

The same total is attained by a type-13 witness. A support-by-support breakdown is supplied in `logs/worst_witness_breakdown.tsv`.

---

## 10. Proof of the main theorem

#### Proof of Theorem 1.1

Assume that an odd distinct covering exists and let \(N\) be the LCM of its moduli. By [HN19], \(3\mid N\). If \(\omega(N)\le6\), Lemma 2.1 permits divisor completion and exponent padding. Lemmas 3.1 and 3.2 reduce the problem to the pure-tower survivor product with exponent-free budgets. Sections 4–7 construct the corrected hierarchical clipped-star upper bound, and Lemma 8.1 reduces every possible support of size at most six to the extremal template \(\{3,5,7,11,13,17\}\).

Proposition 9.1 bounds the covered fraction of the survivor product by

\[
\frac{200282}{200475}<1.
\]

Hence some point of the survivor product remains uncovered, contradicting the assumption that the divisor-complete family covers. Therefore \(\omega(N)\ge7\). ∎

---

## 11. Reproducibility and independent checks

The primary release contains:

- `src/stage1_exact.cpp`, which scans all \(21^5\) shallow states for each profile orbit;
- `src/stage2_exact.cpp`, which scans every selective depth-three refinement of the 2505 critical states;
- `src/tau3_orbit_audit.py`, which regenerates the 42,840 labelled profile vertices and checks the retained 28 representatives;
- `scripts/verify_outputs.py`, which compares every proof-relevant numerator, survivor count, evaluation count, and orbit count with the manifest;
- `scripts/verify_worst_states_fraction.py`, which reevaluates every reported extremal state with exact Python rational arithmetic;
- `scripts/strict_compile.sh`, which compiles both C++ scanners with warnings promoted to errors and syntax-checks every Python verifier.

Running

```bash
bash scripts/run_primary.sh
```

produces the verification report

```text
Stage I records: 28/28
Stage II records: 3/3
Global maximum: 200282/200475
Exact gap: 193/200475
STATUS: PASS
```

A second Python/Numba implementation uses a different representation, independently generates the profile orbits, evaluates outside-support products directly rather than through the C++ subset-product table, and reproduces the same exact Stage-I and Stage-II extrema.

A third formula-only reconstruction is included in `independent/third_formula_reimplementation/`. It was written from (6.1) and (6.2) without consulting the primary evaluation source. It carries all eighteen leaves explicitly, uses no mod-\(9\) aggregation and no Gray-code subset-product table, reproduces all 28 Stage-I maxima and the complete five-coordinate survivor-state lists, and reproduces the three Stage-II maxima. Its orbit generator obtains 42,840 vertices and 28 orbits under a rooted-tree group of order 3,359,232. Exact `Fraction` evaluation again yields \(200282/200475\).

As a regression test rather than a proof, the third implementation also checked Lemma 7.4 on 1,680 deterministic pseudorandom shallow vertices against all \(19^3\) refinements: 11,523,120 comparisons produced no violation and maximum observed \(F_3-F_2=0\). The proof of Lemma 7.4 remains the algebraic argument above; this test guards against an implementation mismatch.

The finite code has a deliberately narrow trust boundary: it verifies Proposition 9.1, while Lemmas 2.1–8.1 are ordinary mathematical claims to be reviewed independently. Agreement with a manifest establishes reproducibility of the enumeration, not the correctness of those analytic reductions.

---

## 12. Discussion

The certificate is not a finite-LCM search. Prime-power exponents have already been replaced by their worst-case limits \(\beta_p=1/(p-2)\), and the computation ranges only over vertices of compact relaxation polytopes. The method may be described as

\[
\text{pure-tower removal}
\;\longrightarrow\;
\text{exact hierarchical skeleton}
\;\longrightarrow\;
\text{outside-support clipping}
\;\longrightarrow\;
\text{adaptive promotion}.
\]

The final numerical gap is small, but it is exact and has survived both a correction to the tail functional and two independently structured reconstructions. It also reflects the economical choice to promote level-three singleton axes only at \(5,7,11\), rather than an apparent intrinsic barrier of the functional. For the displayed type-13 worst witness, keeping the \(5,7,11\) choices fixed and additionally promoting the \(13\)- and \(17\)-axes lowers the worst value over those two new blocks to

\[
\frac{199724}{200475},
\]

with gap \(751/200475\). This is a witness-specific diagnostic, not a replacement for the exhaustive certificate, but it shows that the published gap is partly a consequence of stopping the adaptive promotion early. The small certified gap is therefore a reason for careful external scrutiny, not a source of numerical uncertainty.

This paper deliberately does not claim a solution of the Erdős–Selfridge problem. It proves only a lower bound on the number of distinct prime divisors that a hypothetical odd covering LCM must contain.

---

## Appendix A. Full Stage-I table

All entries have denominator \(601425\).

| type | numerator | critical states |
|---:|---:|---:|
| 0 | 598546 | 0 |
| 1 | 598546 | 0 |
| 2 | 593656 | 0 |
| 3 | 589137 | 0 |
| 4 | 585114 | 0 |
| 5 | 586602 | 0 |
| 6 | 601190 | 0 |
| 7 | 601693 | 30 |
| 8 | 592648 | 0 |
| 9 | 586447 | 0 |
| 10 | 587809 | 0 |
| 11 | 605556 | 1161 |
| 12 | 600418 | 0 |
| 13 | 605556 | 1314 |
| 14 | 596317 | 0 |
| 15 | 600738 | 0 |
| 16 | 596595 | 0 |
| 17 | 592740 | 0 |
| 18 | 593830 | 0 |
| 19 | 590187 | 0 |
| 20 | 592979 | 0 |
| 21 | 592178 | 0 |
| 22 | 594945 | 0 |
| 23 | 598233 | 0 |
| 24 | 593056 | 0 |
| 25 | 597412 | 0 |
| 26 | 597484 | 0 |
| 27 | 595125 | 0 |

---

## Appendix B. Disclosure of computational and AI assistance

Computer algebra and exact enumeration were used throughout the development and verification of the certificate. Generative-AI systems were used extensively for exploratory mathematics, code drafting, adversarial review, a formula-only independent reimplementation, and prose preparation. The final claim rests on the explicit mathematical reductions and the released exact-arithmetic programs; responsibility for the argument and its presentation remains with the author.

---

## References

[BFF86] M. A. Berger, A. Felzenbaum, and A. S. Fraenkel, *Necessary condition for the existence of an incongruent covering system with odd moduli*, Acta Arithmetica **45** (1986), 375–379. DOI: 10.4064/aa-45-4-375-379.

[BFF87] M. A. Berger, A. Felzenbaum, and A. S. Fraenkel, *Necessary condition for the existence of an incongruent covering system with odd moduli II*, Acta Arithmetica **48** (1987), 73–79. DOI: 10.4064/aa-48-1-73-79.

[BBMST21] P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, and M. Tiba, *The Erdős–Selfridge problem with square-free moduli*, Algebra & Number Theory **15** (2021), 609–626. DOI: 10.2140/ant.2021.15.609.

[BBMST22] P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, and M. Tiba, *On the Erdős covering problem: the density of the uncovered set*, Inventiones Mathematicae **228** (2022), 377–414. DOI: 10.1007/s00222-021-01087-5.

[GS05] S. Guo and Z.-W. Sun, *On odd covering systems with distinct moduli*, Advances in Applied Mathematics **35** (2005), 182–187. DOI: 10.1016/j.aam.2005.01.004.

[HN19] R. D. Hough and P. P. Nielsen, *Covering systems with restricted divisibility*, Duke Mathematical Journal **168** (2019), 3261–3295. DOI: 10.1215/00127094-2019-0058.

[MS26] I. Mian and S. Siddique, *Kernel-checked exclusions for the Erdős–Selfridge odd covering problem: any odd covering of \(\mathbb Z\) has lcm exceeding 10000*, arXiv:2607.25628 (2026).

[BCHLPSW26] C. Bispels, M. Cohen, J. Harrington, J. Lowrance, K. Pontes, L. Schaumann, and T. W. H. Wong, *A further investigation on covering systems with odd moduli*, Discrete Mathematics **349** (2026), Article 115013; arXiv:2507.16135.
