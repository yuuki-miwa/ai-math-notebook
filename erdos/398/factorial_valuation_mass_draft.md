# Logarithmic mass of factorial prime-power blocks in fixed valuation residue classes

Internal verification draft; status updated 2026-09-06. Not submitted or published.

The qualitative proof below is retained. The current
[quantitative verification draft](mass_formula_improvement_round2_ja.md), in Japanese,
proposes an error O_m(n(log n)^(3/4)(log log log n)^(1/4)), uniformly in
interval endpoints. It rederives a prime exponential-sum bound using Sander's
Lemma 7 and Vaughan's identity, and handles nonnegative boundary errors over
all integers. The [integration audit](mass_formula_round2_audit_ja.md) records
corrections and verification limits. The
[earlier 8/9 appendix](factorial_valuation_mass_quantitative.md) is preserved.
None of these drafts has independent human mathematical review; the fixed-parameter
lemma below by itself does not justify either quantitative strengthening.

This is a proposed deduction from Sander's Proposition 1 [S]. Its application
has been checked internally against the original pages, but has not received
independent human mathematical review. Novelty is unresolved. In particular, the
relationship to [BH, Conjecture 5.1] below is a reason to request scrutiny, not
a claim that the conjecture remains open or that priority has been established.
This draft was prepared through human--AI collaboration; no authorship or
third-party endorsement is asserted.

## 1. Proposed statement

Write e_p(n)=v_p(n!) and L_n=log(n!). All logarithms are natural. For fixed
integers m>=2 and c, and fixed real numbers 0<=a<b<=1, the proposed result is

\[
M_{m,c}(n;a,b):=
\sum_{\substack{n^a<p\le n^b\\e_p(n)\equiv c\pmod m}}
e_p(n)\log p
=\left(\frac{b-a}{m}+o(1)\right)L_n.
\tag{1}
\]

The limit is through all positive integers n. No average over n is taken.
No uniformity in a growing m is asserted. In particular, (1) assigns mass
(1/m+o(1))L_n to each valuation residue class on the whole prime range.

## 2. The exponential-sum input and its quantifiers

Let e(t)=exp(2 pi i t). In the notation preceding [S, Proposition 1],
J>8, 1<=j=j_1<...<j_r<=J are integers, the h_i are real,
h_1>=1, and H=max_i |h_i|. The proposition, on printed page 109, gives

\[
\left|\sum_{p\le N}
e\!\left(x\sum_{i=1}^r h_i p^{-j_i}\right)\right|
\le C^J\left[
N^{1-\kappa v_5(J)\Lambda(N,xH)}
+N^{(j+2)/2}x^{-1/2}+N^{5/6}H^2
\right](\log(xH))^{4J},
\tag{2}
\]

provided

\[
\exp(CJ(\log(2J))^3)\le N\le x^{1/j},
\qquad
\Lambda(U,V)=\left(\frac{\log U}{\log V}\right)^2,
\qquad v_5(J)=J^{-5}(\log(2J))^{-2}.
\]

Here C,kappa are the positive constants supplied by [S], with its small
constant renamed to distinguish it from the residue c. The common notation is on printed
page 97. In particular, j in both the upper bound for N and the second error
term is the **smallest nonzero exponent**, not J.

Fix R>=1 and a nonzero vector h in Z^R. Set j=min{r:h_r!=0}.
For fixed 0<alpha<beta<1/j we claim

\[
\sup_{n^\alpha\le T\le n^\beta}
\frac{\log T}{T}
\left|\sum_{p\le T}
e\!\left(\frac nm\sum_{r=1}^R h_r p^{-r}\right)\right|
\longrightarrow0.
\tag{3}
\]

Delete zero coefficients and, if the first nonzero coefficient is negative,
take complex conjugates. That coefficient is now a positive integer, hence
at least 1. Apply (2) with x=n/m and J=max(9,R). All coefficients and J are
fixed as n grows. Its lower bound holds eventually, and beta<1/j ensures
n^beta<=(n/m)^(1/j) eventually. Uniformly in the indicated range,
log T/log(nH/m)>=alpha/2 for large n. With c_J=kappa v_5(J)>0, the normalized
right side of (2) is at most

\[
O_{R,h,m,\alpha,\beta}\!\left[
\left(n^{-c_J\alpha^3/4}
+n^{-(1-\beta j)/2}+n^{-\alpha/6}\right)
(\log n)^{4J+1}\right]=o(1).
\]

This proves (3), including its uniformity in T. It does not allow the Fourier
frequencies or R to grow with n.

## 3. A band avoiding reciprocal endpoints

Fix R and

\[
\frac1{R+1}<\alpha<\beta<\frac1R.
\tag{4}
\]

For primes n^alpha<p<=n^beta, Legendre's formula is exactly

\[
e_p(n)=\sum_{r=1}^R\left\lfloor\frac n{p^r}\right\rfloor.
\tag{5}
\]

Define, for **all** primes p, the vector

\[
z_{n,p}=\left(\left\{\frac n{mp}\right\},\ldots,
\left\{\frac n{mp^R}\right\}\right)\in[0,1)^R.
\]

For every fixed nonzero integer Fourier vector, its smallest nonzero exponent
j satisfies beta<1/R<=1/j. Thus (3), together with the prime number theorem,
gives equidistribution of z_{n,p} over p<=T, uniformly for
n^alpha<=T<=n^beta.

For clarity about the moving family of point sets: fix an approximation
accuracy first. Continuous periodic upper and lower approximations to the
indicator of any fixed box can be chosen with arbitrarily small difference
of integrals. Their Fourier approximations use finitely many fixed modes.
Apply (3) to these modes, let n tend to infinity, then let the approximation
accuracy tend to zero. This proves convergence for each fixed box, uniformly
in T in the stated range, and
also handles points lying on the boundaries of boxes.

Define the bounded step function

\[
g_c(z)={\bf1}_{\{\sum_{r=1}^R\lfloor mz_r\rfloor\equiv c\pmod m\}}.
\]

It is a union of m^(R-1) boxes of volume m^(-R), so its integral is 1/m.
For any real y, floor(y) is congruent to floor(m{y/m}) modulo m. Hence (5)
shows that g_c(z_{n,p}) is the required residue indicator within the band.
Uniformly for T in the indicated range,

\[
C_n(T):=\sum_{p\le T}\left(g_c(z_{n,p})-\frac1m\right)
=o(T/\log T).
\tag{6}
\]

Outside the band g_c is only a proxy for the true valuation indicator.
The same proxy is used consistently in the prefix sum C_n(T); no claim
that the R-term formula equals e_p(n) for all p<=T is needed.

## 4. Passing from counts to logarithmic mass

Put A=n^alpha, B=n^beta, w(t)=log(t)/t. Partial summation, using the
uniform bound (6), gives

\[
\sum_{A<p\le B}\left(g_c(z_{n,p})-\frac1m\right)
\frac{\log p}{p}=o(\log n).
\tag{7}
\]

Indeed, with |C_n(t)|<=epsilon_n t/log t and epsilon_n->0, the boundary
terms are O(epsilon_n), and the integral is
O(epsilon_n integral_A^B dt/t)=o(log n). The prime number theorem gives

\[
\sum_{A<p\le B}\frac{\log p}{p}
=(\beta-\alpha)\log n+o(\log n).
\]

Within the band (5) also gives

\[
e_p(n)=\frac np+O_R\!\left(\frac n{p^2}+1\right).
\]

Chebyshev's bound implies

\[
\sum_{A<p\le B}
\left|e_p(n)-\frac np\right|\log p
\ll_R n/A+B=o(n\log n).
\]

Combining these facts and L_n~n log n proves

\[
M_{m,c}(n;\alpha,\beta)
=\left(\frac{\beta-\alpha}{m}+o(1)\right)L_n
\quad\text{under (4).}
\tag{8}
\]

## 5. Exhausting an arbitrary fixed interval

First, for any fixed 0<=t<=1,

\[
\sum_{p\le n^t}e_p(n)\log p=(t+o(1))L_n.
\tag{9}
\]

For t=0 the sum is empty. For t>0, Legendre's formula gives
|e_p(n)-n/(p-1)|=O(log n/log p), uniformly for p<=n. Summing the weighted
errors over p<=n^t gives O(pi(n^t)log n)=O_t(n^t).
Also, by partial summation from the prime number theorem,
sum_{p<=y} log p/(p-1)=log y+o(log y). This proves (9).
Consequently the total mass on (n^a,n^b] is ((b-a)+o(1))L_n,
including a=0 or b=1.

Fix epsilon>0. Choose finitely many disjoint closed intervals
[alpha_i,beta_i] inside (a,b), each strictly inside some
(1/(R_i+1),1/R_i), whose total length ell is greater than b-a-epsilon.
This is possible by first truncating the reciprocal endpoints near 0 and
then deleting small neighborhoods of the finitely many remaining endpoints.
The bands, their number and the R_i are all fixed before n tends to infinity.

By (8), the residue-c mass on these bands is (ell/m+o(1))L_n. By (9),
the omitted total mass is (b-a-ell+o(1))L_n. Positivity therefore gives

\[
\frac\ell m
\le\liminf_{n\to\infty}\frac{M_{m,c}(n;a,b)}{L_n}
\le\limsup_{n\to\infty}\frac{M_{m,c}(n;a,b)}{L_n}
\le\frac\ell m+(b-a-\ell).
\]

Letting epsilon tend to zero proves (1). This is an iterated limit, not an
application of (2) with a growing number of terms.

## 6. Scope of the proposed consequence

If E is any fixed finite set of positive valuations, its total mass is
O_E(n): for each d in E,
sum_{p:e_p(n)=d} e_p(n)log p <= d theta(n)=O_d(n).
Thus changing a valuation set at finitely many integers does not change
its normalized mass.

A finite union of arithmetic progressions in the positive integers is
eventually periodic. Apply (1) with a common period (period 1 follows
directly from (9)), sum over its residue classes, and ignore its finite
exceptional set. For such a set E with natural density delta(E), this yields

\[
\log\prod_{\substack{n^a<p\le n^b\\e_p(n)\in E}}p^{e_p(n)}
=\big((b-a)\delta(E)+o(1)\big)L_n.
\tag{10}
\]

With a=1-beta and b=1-beta_1, this is precisely the assertion formulated as
[BH, Conjecture 5.1, p.1758]. This identifies a possible substantive
contribution **if the deduction and its novelty survive independent review**.

For example, in n!=x^2(x+1), x>0, the two factors are coprime. Every prime
dividing x therefore has even e_p(n), so 2log x<=M_{2,0}(n;0,1).
Along any unbounded sequence of solutions, the equation gives
2log x=(2/3+o(1))L_n, while (1) would give an upper bound
(1/2+o(1))L_n. Thus (1) implies finiteness of the solutions of this equation,
without giving a numerical cutoff or a list of all solutions.

No result about n!=x^2-1 follows from this example. In particular, (1) does
not exclude the outstanding k=2 branch n!=4u^2(u^2-1) in our #398 notebook:
the forced odd-valuation mass and the receiving factor both have leading
coefficient 1/2. It also provides no estimate for characters whose
conductors move with n.

## 7. Novelty correction concerning the k=3 motivation

The eventual exclusion of n!=(u^2-1)(4u^2-3)^2 is **not presented as new**.
Apply [BH, Theorem 4.1] to P(X)=(X^2-1)(4X^2-3)^2 and its divisor
Q(X)=(4X^2-3)^2. Except for 2 and 3, primes for which Q has a root are
exactly those with (3/p)=1, or p=1,11 mod 12. Their density is 1/2,
whereas deg Q/deg P=4/6. The theorem therefore gives finiteness directly.
Neither a fundamental Pell-unit condition nor the proposed mass theorem
is required for this conclusion.

### A distinction from unweighted prime counts

The assertion concerns the weight e_p(n)log p, not equal numbers of primes.
In fact, the fraction of primes p<=n for which e_p(n) is odd tends to log 2,
not 1/2. To see this, fix a cutoff D. For each 1<=r<=D and sufficiently
large n, e_p(n)=r on n/(r+1)<p<=n/r, so the prime number theorem assigns
limiting proportion 1/(r(r+1)). All other primes lie below n/(D+1),
with limiting upper proportion at most 1/(D+1). Letting D grow gives
sum_{r odd} 1/(r(r+1))=log 2. This does not conflict with (1): primes
of size comparable with n contribute only O(n) to logarithmic block mass.

## 8. Questions for an independent reader

1. Does (2), with all the common hypotheses of [S], justify (3) for every
   fixed Fourier vector? Is there a relevant correction to [S]?
2. Are the uniform prefix-sum and discontinuous-indicator arguments in
   Sections 3--4 valid, in particular the use of the R-term proxy?
3. Is the order of limits in Section 5 sufficient for all endpoints,
   without any hidden uniformity in R?
4. Is (1), (10), or an equivalent statement already available in the
   literature following [S] or [BH]?

No external review or exhaustive citation search has been completed.
The original pages used to check [S] are PDF pages 13 and 25 (printed
pages 97 and 109) of the user-provided kore.pdf. Finite numerical tests
in the surrounding project do not verify an asymptotic theorem.

## References

[S] J. W. Sander, *On the order of prime powers dividing the middle binomial
coefficient*, Acta Mathematica **174** (1995), 85--118.
[DOI](https://doi.org/10.1007/BF02392802).
The title on the original uses the binomial symbol (2n choose n).

[BH] D. Berend and J. E. Harmse, *On Polynomial-Factorial Diophantine
Equations*, Transactions of the American Mathematical Society **358**
(2006), 1741--1779.
[DOI](https://doi.org/10.1090/S0002-9947-05-03780-3);
[author-uploaded text](https://www.researchgate.net/publication/261826784_On_Polynomial-Factorial_Diophantine_Equations).
