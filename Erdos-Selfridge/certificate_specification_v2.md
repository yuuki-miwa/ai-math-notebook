# Exact certificate specification for the seven-prime obstruction

**Version 2 — 4 September 2026**

This document fixes the finite functions evaluated by `src/stage1_exact.cpp` and `src/stage2_exact.cpp`. It is intended to let a reviewer reconstruct the computational proposition without reverse-engineering the source code.

## 1. Constants and indexing

The five non-3 primes are ordered as

\[
P=(5,7,11,13,17).
\]

Their exponent-free budgets are

\[
\boldsymbol\beta=
\left(\frac13,\frac15,\frac19,\frac1{11},\frac1{15}\right).
\]

Write

\[
(d_0,d_1,d_2,d_3,d_4)=(3,5,9,11,15),
\qquad
D=\prod_{i=0}^4d_i=22275,
\]

and

\[
\mathrm{DEN}=27D=601425.
\]

A support is encoded by a nonempty bit mask

\[
T\in\{1,\ldots,31\}.
\]

Its complement within the five coordinates is `31 xor T`.

The 18 mod-27 leaves are indexed by

\[
a=0,1,\ldots,17.
\]

Define

\[
\operatorname{node}(a)=\left\lfloor\frac a3\right\rfloor\in\{0,\ldots,5\},
\qquad
\operatorname{branch}(a)=\left\lfloor\frac a9\right\rfloor\in\{0,1\}.
\]

A profile representative is an integer vector

\[
w=(w_0,\ldots,w_{17})\in\{0,1,2\}^{18},
\qquad
\sum_aw_a=27,
\]

representing \(\tau_a=w_a/27\).

## 2. Stage-I axis states

For each non-3 prime coordinate \(i\), a shallow state is a pair

\[
(r_i,n_i)\in\{-1,0,1\}\times\{-1,0,1,2,3,4,5\}.
\]

Here `-1` means the zero vertex of the relevant simplex. The source code numbers these 21 pairs by

\[
s_i=7(r_i+1)+(n_i+1)\in\{0,\ldots,20\}.
\]

For a mod-9 node \(j\in\{0,\ldots,5\}\), define

\[
Q_{i,j}=d_i-
\mathbf1_{\{r_i=\lfloor j/3\rfloor\}}
-
\mathbf1_{\{n_i=j\}}.
\]

For every leaf \(a\), the corresponding normalized complement factor is \(q_{i,a}=Q_{i,\operatorname{node}(a)}/d_i\). These factors are nonnegative: at Stage I at most two unit subtractions occur, and \(d_i\ge3\).

For each node define the profile aggregates

\[
A_j=\sum_{a: \operatorname{node}(a)=j}w_a,
\qquad
M_j=\max_{a: \operatorname{node}(a)=j}w_a.
\]

For a support mask \(T\), put

\[
R_{T,j}=\prod_{i\notin T}Q_{i,j}.
\]

The empty outside product is one.

## 3. Stage-I integer numerator

The exact skeleton numerator is

\[
S_1=\sum_{j=0}^{5}A_j
\left(D-\prod_{i=0}^4Q_{i,j}\right).
\]

For every nonempty support \(T\), define

\[
G_0(T)=\sum_j A_jR_{T,j},
\]

\[
G_1(T)=\max_{b\in\{0,1\}}
\sum_{j:\lfloor j/3\rfloor=b}A_jR_{T,j},
\]

\[
G_2(T)=\max_j A_jR_{T,j},
\qquad
G_3(T)=\max_j M_jR_{T,j},
\]

and

\[
H(T)=\max_jR_{T,j}.
\]

The Stage-I score numerator is

\[
\boxed{
\mathcal N_1(w,s)=
S_1+
\sum_{\substack{\varnothing\ne T\subseteq P\\ |T|\ge2}}
\bigl(G_0(T)+G_1(T)+G_2(T)\bigr)
+
\sum_{\varnothing\ne T\subseteq P}G_3(T)
+
\sum_{\varnothing\ne T\subseteq P}H(T).
}
\]

The corresponding covered-fraction upper bound is

\[
F_2=\frac{\mathcal N_1}{601425}.
\]

Why the budget coefficients disappear from the displayed numerator: multiplying the mathematical term \(B_TR_{T,a}\) by \(D=\prod_i d_i\) cancels the factors \(1/d_i\) for \(i\in T\), leaving precisely the outside product \(\prod_{i\notin T}Q_{i,a}\). The factor \(27\) clears \(\tau_a=w_a/27\), and the tail coefficient \(1/27\) is simultaneously cleared by the same denominator.

A shallow state is retained exactly when

\[
\mathcal N_1\ge601425.
\]

## 4. Stage-II promotion states

Stage II promotes the level-three singleton axes for the first three coordinates, corresponding to \(5,7,11\). For \(i=0,1,2\), choose

\[
c_i\in\{-1,0,1,\ldots,17\}.
\]

Again, `-1` is the zero simplex vertex. Coordinates \(i=3,4\), corresponding to \(13,17\), are not promoted.

For every leaf \(a\), define

\[
Q_{i,a}=d_i-
\mathbf1_{\{r_i=\operatorname{branch}(a)\}}
-
\mathbf1_{\{n_i=\operatorname{node}(a)\}}
-
\mathbf1_{\{i\le2\}}\mathbf1_{\{c_i=a\}}.
\]

For a support \(T\), put

\[
R_{T,a}=\prod_{i\notin T}Q_{i,a}.
\]

Here at most three unit subtractions occur in any \(Q_{i,a}\). Since \(d_0=3\), the smallest possible value is zero; no factor is negative.

## 5. Stage-II integer numerator

The exact skeleton numerator is

\[
S_2=\sum_{a=0}^{17}w_a
\left(D-\prod_{i=0}^4Q_{i,a}\right).
\]

For each nonempty support \(T\), define

\[
G_0(T)=\sum_aw_aR_{T,a},
\]

\[
G_1(T)=\max_{b\in\{0,1\}}
\sum_{a:\operatorname{branch}(a)=b}w_aR_{T,a},
\]

\[
G_2(T)=\max_{j\in\{0,\ldots,5\}}
\sum_{a:\operatorname{node}(a)=j}w_aR_{T,a},
\]

\[
G_3(T)=\max_aw_aR_{T,a},
\qquad
H(T)=\max_aR_{T,a}.
\]

Let \(e_i\) denote the singleton support at coordinate \(i\). Then

\[
\boxed{
\begin{aligned}
\mathcal N_2(w,s,c)
={}&S_2
+
\sum_{\substack{\varnothing\ne T\subseteq P\\ |T|\ge2}}
\bigl(G_0(T)+G_1(T)+G_2(T)+G_3(T)\bigr)\\
&+G_3(e_3)+G_3(e_4)
+
\sum_{\varnothing\ne T\subseteq P}H(T).
\end{aligned}
}
\]

The corresponding Stage-II covered-fraction upper bound is

\[
F_3=\frac{\mathcal N_2}{601425}.
\]

The singleton \(G_3\)-terms for \(e_0,e_1,e_2\) are absent because those level-three families have been promoted into the exact skeleton. The singleton terms for \(e_3,e_4\) remain residual. The corrected deep tail \(H(T)\) is retained for every nonempty support and maximizes over all 18 leaves, including zero-profile leaves.

## 6. Exhaustive domain

The profile polytope has 42,840 labelled vertices and 28 rooted-tree orbits. Stage I evaluates

\[
28\cdot21^5=114,354,828
\]

product vertices. Exactly 2,505 shallow states satisfy \(\mathcal N_1\ge601425\), distributed as 30, 1,161 and 1,314 states among profile types 7, 11 and 13. The release driver does not assume these type labels: it derives the Stage-II type list from the nonempty Stage-I survivor files, after which the manifest verifier checks that the resulting list is exactly \(\{7,11,13\}\).

For each retained state, Stage II evaluates

\[
19^3=6,859
\]

promotion vertices, for a total of

\[
2,505\cdot6,859=17,181,795
\]

integer evaluations.

## 7. Expected exact output

The Stage-II maxima are

\[
597601,
\qquad
600846,
\qquad
600846
\]

for profile types 7, 11 and 13, respectively. Hence

\[
\max\mathcal N_2=600846<601425,
\]

or, after reduction,

\[
\boxed{
\max F_3=
\frac{600846}{601425}
=
\frac{200282}{200475}
<1.
}
\]

The exact gap is

\[
\boxed{
1-\max F_3=
\frac{579}{601425}
=
\frac{193}{200475}.
}
\]

## 8. Independent reconstruction and trust boundary

The primary scanners use integer arithmetic and a compressed representation. The release also contains two independently structured reconstructions. The formula-only reconstruction in `independent/third_formula_reimplementation/` carries all 18 leaves explicitly and forms every outside-support product directly. It reproduces all 28 Stage-I maxima, the full five-coordinate survivor-state lists for the three critical types, and all three Stage-II maxima.

The manifest is an expected-output record. Agreement with it demonstrates deterministic reproducibility of the stated finite enumeration; it is not an independent proof of the analytic reductions leading to the functionals above. Those reductions remain the mathematical trust boundary.

The supplied promotion stress test is likewise a regression check rather than the proof of Lemma 7.4. Its retained full run examines 1,680 shallow states against 11,523,120 Stage-II refinements and finds no violation.

## 9. Formula-to-code map

| Mathematical object | Primary implementation |
|---|---|
| \(w_a,A_j,M_j\) | `stage1_exact.cpp`, `tv`, `agg`, `mx` |
| shallow \((r_i,n_i)\) | `PState`, `states`, `ss` |
| \(Q_{i,j}\) | `fac[i][s][a]` |
| \(R_{T,j}\) | `subset_products[a][outside]` |
| \(S_1\) | first `score` loop in Stage I |
| \(G_0,G_1,G_2,G_3,H\) | `g0`, `branch0/1`, `g2`, `g3`, `tail` |
| \(c_i,Q_{i,a}\) | `choice`, `promoted`, `q` in Stage II |
| \(S_2\) | first `total` loop in `Evaluator::score` |
| Stage-II \(G_0,G_1,G_2,G_3,H\) | `g0`, `branches`, `nodes`, `g3`, `tail` |
| threshold \(601425\) | `DEN` |

No floating-point value is used in a proof-relevant comparison. Decimal values are printed only after the integer maximum has been determined.
