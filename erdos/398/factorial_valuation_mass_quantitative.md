# A quantitative version of the factorial valuation-mass formula

Historical 8/9 version, retained for comparison. The current stronger
[3/4 verification draft](mass_formula_improvement_round2_ja.md) and its
[integration audit](mass_formula_round2_audit_ja.md) are separate files.
The proof below is unchanged by that integration and is not externally reviewed.

Internal verification appendix, revised 2026-09-05 after a user-supplied
Claude review. Not independently reviewed by a mathematician.

This appendix proposes a strengthening of
[the qualitative draft](factorial_valuation_mass_draft.md). It uses the full
parameter dependence of Sander's Proposition 1, not the fixed-parameter
little-o consequence alone. Correctness and novelty still require external
review. The Fourier coefficient norm is tracked below; the resulting rate
improves the first version's exponent 11/12. No optimality is claimed.

Update 2026-09-06: a [further bounded round](mass_formula_improvement_round_ja.md)
gives an alternative pointwise Fourier approximation with
H=ceil(m^2 K^8) and coefficient norm exp(O_m(K log log K)). It does not
improve (Q1) using the present exponential-sum bound. The proof below is
retained unchanged; the new construction and its boundary-mode limitation
are recorded separately.

## 1. Proposed bound

For each fixed integer m>=2, uniformly in c mod m and 0<=a<b<=1,

\[
\boxed{\quad
\sum_{\substack{n^a<p\le n^b\\v_p(n!)\equiv c\pmod m}}
v_p(n!)\log p
=\frac{b-a}{m}\log(n!)
+O_m\!\left(n(\log n)^{8/9}(\log\log n)^{1/3}\right).
\quad}
\tag{Q1}
\]

The interval endpoints may therefore vary with n. The modulus m is fixed.
The implied constant and a numerical starting point have not been evaluated;
this is a specified error order, not a numerical exclusion threshold.

Set L=log n and

\[
K=\left\lfloor\rho_m\left(\frac{L}{(\log L)^3}\right)^{1/9}\right\rfloor,
\]

where 0<rho_m<=1 is a sufficiently small fixed constant, chosen in Section 3.
Assume n is sufficiently large in terms of m, so K>=9. Define

\[
d=\frac1{10K^3},\qquad
\alpha_R=\frac1{R+1}+d,\quad
\beta_R=\frac1R-d\quad(1\le R\le K).
\tag{Q2}
\]

These bands are nonempty and disjoint. Their total length is

\[
\ell_K=1-\frac1{K+1}-2Kd=1-O(1/K).
\tag{Q3}
\]

Throughout a band, Legendre's formula has exactly R terms.

## 2. A finite Fourier approximation with dimension tracked

Put

\[
\delta=\frac1{m^K K^4},\qquad
H=\left\lceil m^{2K}K^8\right\rceil.
\tag{Q4}
\]

Here H is a Fourier cutoff, not an unspecified growing parameter in a
little-o estimate. In R-dimensional torus coordinates define

\[
g_{R,c}(z)={\bf1}_{\{\sum_{r=1}^R\lfloor mz_r\rfloor\equiv c\pmod m\}}.
\]

It is the sum of the indicators of m^(R-1) disjoint half-open boxes,
each with side length 1/m.

We construct trigonometric polynomials P^- and P^+ such that

\[
P^-\le g_{R,c}\le P^+,\qquad
\left|\widehat P^\pm(0)-\frac1m\right|\ll K^{-3}.
\tag{Q5}
\]

Both have frequencies ||h||_infinity<=H, and each nonconstant coefficient
has absolute value at most m^(R-1), hence at most m^K.

Here is the construction, including boundary points. The normalized
one-dimensional Fejer kernel F_H is nonnegative, has integral 1, has Fourier
support [-H,H], and satisfies

\[
\int_{\|t\|\ge\delta}F_H(t)\,dt\ll\frac1{H\delta}.
\tag{Q6}
\]

This follows immediately from
F_H(t)=(H+1)^(-1)(sin(pi(H+1)t)/sin(pi t))^2 and
|sin(pi t)|>=2||t||. For the product kernel on the R-dimensional torus,
the mass outside ||t||_infinity<delta is at most eta=C R/(H delta),
with an absolute C, by the union bound.

For a box B let B^+ be its coordinatewise delta-enlargement on the torus
and B^- its delta-contraction. Then

\[
P_B^+={\bf1}_{B^+}*F_H^{\otimes R}+\eta,
\qquad
P_B^-={\bf1}_{B^-}*F_H^{\otimes R}-\eta
\]

majorize and minorize its half-open indicator pointwise. This remains true
on the boundary: for x in B the enlarged box contains x-t whenever
||t||_infinity<delta; for x outside B the contracted box contains no such
x-t. The difference of the integrals from vol(B) is
O(R delta+R/(H delta)); the volume estimate follows by telescoping the
products of side lengths, which all lie in [0,1]. Every nonconstant
Fourier coefficient has absolute value at most 1.

Sum these polynomials over the m^(R-1) boxes. Equations (Q4) give

\[
m^{R-1}\left(R\delta+\frac{R}{H\delta}\right)
\ll K^{-3},
\]

proving (Q5).

We need the sum of the absolute Fourier coefficients, not the number of
modes times the largest coefficient. For any interval I on the circle,
including one that crosses 0,

\[
|\widehat{{\bf1}_I}(u)|\le\min\left(|I|,\frac1{\pi|u|}\right)
\quad(u\ne0),\qquad
|\widehat F_H(u)|\le1.
\]

The first inequality follows by integrating exp(-2 pi i u t) over I.
It implies

\[
\sum_{|u|\le H}|\widehat{{\bf1}_I}(u)\widehat F_H(u)|
\le1+\frac2\pi\sum_{u=1}^H\frac1u
\le C_0(2+\log H),
\]

with an absolute C_0. Fourier coefficients of a product box factor, so
the corresponding norm for each convolved box is at most
[C_0(2+log H)]^R. The constants +eta and -eta affect only frequency zero.
Thus the sum of the absolute nonconstant coefficients of either P^+ or P^-
is at most m^(R-1)[C_0(2+log H)]^R. No cancellation between boxes is needed.

## 3. Sander's bound for all frequencies actually used

Write

\[
z_{n,p}=\left(\{n/(mp)\},\ldots,\{n/(mp^R)\}\right),\qquad
S_h(T)=\sum_{p\le T}e\!\left(\frac nm\sum_{r=1}^R h_rp^{-r}\right).
\]

Here e(t)=exp(2 pi i t). The encoding of the valuation is the elementary
identity

\[
\left\lfloor m\{y/m\}\right\rfloor
=\lfloor y\rfloor\bmod m,
\]

where the right side is the least nonnegative residue. Indeed, writing
y/m=q+theta with q an integer and 0<=theta<1 gives
floor(y)=mq+floor(m theta). Applying this with y=n/p^r and using all R
nonzero terms of Legendre's formula proves, inside the R-th band,

\[
g_{R,c}(z_{n,p})={\bf1}_{\{v_p(n!)\equiv c\pmod m\}}.
\]

We record the input with its parameters. On printed p.97, Sander defines

\[
\Lambda(X,Y)=\left(\frac{\log X}{\log Y}\right)^2,
\qquad v_5(J)=J^{-5}(\log(2J))^{-2}.
\]

For J>8, positive integers 1<=j=j_1<...<j_q<=J, real coefficients
a_1>=1 and H_*=max_i |a_i|, Proposition 1 (printed p.109) states

\[
\left|\sum_{p\le N}e\!\left(x\sum_{i=1}^q a_i p^{-j_i}\right)\right|
\le C^J\left[
N^{1-\kappa_0 v_5(J)\Lambda(N,xH_*)}
+N^{(j+2)/2}x^{-1/2}+N^{5/6}H_*^2
\right](\log(xH_*))^{4J},
\]

provided exp(CJ(log(2J))^3)<=N<=x^(1/j). Here C and kappa_0>0
are absolute constants, with C sufficiently large. The common parameter J
may be real in the source; only integer choices are needed here.

For every nonzero integer h with ||h||_infinity<=H, delete zero
coefficients and take a conjugate if necessary. Keep the original exponents
of the remaining terms: the source allows gaps in j_1<...<j_q. Its first
coefficient is then >=1. Use the proposition with x=n/m and J=max(9,R)<=K.
The source states on printed page 87 that constants are absolute unless
otherwise indicated; retaining this parameter dependence is essential here.

Let j be the smallest nonzero exponent. Uniformly for
n^alpha_R<=T<=n^beta_R the hypotheses hold, since

\[
\log T\ge\frac L{K+1},\qquad
\frac L{K+1}\gg K(\log(2K))^3,
\qquad
1-\beta_R j\ge Rd\ge d,\qquad dL>\log m
\]

eventually. The last two inequalities imply T<=x^(1/j).
Also log(xH)<=2L eventually for fixed m. In particular,

\[
v_5(J)\Lambda(T,xH)\log T
\ge\frac{L}{4(K+1)^3K^5(\log(2K))^2}
\gg\frac{L}{K^8(\log(2K))^2}.
\]

The other two terms, after division by T, are at most
m^(1/2)exp(-dL/2) and H^2 exp(-L/(6(K+1))), respectively.
The prefactor C^J(log(xH))^(4J) log T is exp(O(K log L)).
Thus the source bound, divided by T/log T, gives

\[
\frac{\log T}{T}|S_h(T)|
\le \exp(O_m(K\log L))
\left[
\exp\!\left(-\frac{\kappa L}{K^8(\log(2K))^2}\right)
+\exp\!\left(-\frac{L}{20K^3}\right)
+\exp\!\left(-\frac{L}{6(K+1)}+2\log H\right)
\right].
\tag{Q7}
\]

Here kappa>0 is an absolute constant, not the residue c. All constants are
independent of R, h and T in the stated ranges.
This also bounds modes whose actual coefficient maximum is less than H:
using H only increases the logarithmic and H^2 losses and weakens the
first exponential saving.

By Section 2 the nonconstant coefficient cost is at most

\[
\sum_{h\ne0}|\widehat P^\pm(h)|
\le m^K[C_0(2+\log H)]^K
=\exp(O_m(K\log K)),
\tag{Q8}
\]

because log H=O_m(K) for K>=9. Fix A_m>0 so that all positive logarithmic
costs in (Q7)--(Q8), including 2 log H, are at most A_m K log L for large n.
This can be done throughout 9<=K<=L^(1/9), before choosing rho_m. Choose
0<rho_m<=1 so that kappa/rho_m^9>=A_m+2. Our choice of K then gives,
for large n,

\[
K^9(\log(2K))^2\log L\le\rho_m^9L,
\qquad
\frac{\kappa L}{K^8(\log(2K))^2}
\ge(A_m+2)K\log L.
\]

Here we used log(2K)<=log L. The second and third negative exponents in
(Q7) have orders L^(2/3)log L and L^(8/9)(log L)^(1/3), respectively,
which both dominate K log L. Thus (Q7) times the bound in (Q8) is
<=K^(-4) for all sufficiently large n. At this optimized scale a fixed
strict constant margin, not a ratio tending to infinity for the first
saving, is what the choice of rho_m ensures.

Using (Q5), and Chebyshev's bound pi(T)<<T/log T for the constant-term
error, now proves the uniform prefix estimate

\[
\left|\sum_{p\le T}\left(g_{R,c}(z_{n,p})-\frac1m\right)\right|
\ll_m K^{-3}\frac{T}{\log T}
\qquad(n^{\alpha_R}\le T\le n^{\beta_R}).
\tag{Q9}
\]

As in the qualitative proof, the R-term proxy is defined on all primes;
it equals the true valuation indicator only inside the R-th band.

## 4. Uniform elementary weight estimates

We use the form of Mertens' estimate

\[
\sum_{p\le y}\frac{\log p}{p}=\log y+O(1)\quad(y\ge2).
\tag{Q10}
\]

For completeness, the identity
log(N!)=sum_{d<=N} Lambda(d) floor(N/d), together with
sum_{d<=N} Lambda(d)=O(N), gives
sum_{d<=N} Lambda(d)/d=log N+O(1). Removing prime powers of exponent
at least 2 costs O(1), proving (Q10), also for real y by rounding.
Here the one-variable Lambda(d) is the von Mangoldt function, distinct
from Sander's two-variable Lambda(X,Y) above.
Thus no untracked uniform prime-number-theorem error is being used here.

For any subinterval [s,t] of [alpha_R,beta_R], partial summation of
(Q9), with w(v)=log(v)/v, yields

\[
\left|\sum_{n^s<p\le n^t}
\left(g_{R,c}(z_{n,p})-\frac1m\right)\frac{\log p}{p}\right|
\ll_m K^{-3}((t-s)L+1)
\quad(\alpha_R\le s<t\le\beta_R).
\tag{Q11}
\]

The boundary terms contribute O_m(K^(-3)) and the integral is bounded
by O_m(K^(-3)) integral_{n^s}^{n^t} dv/v.
Legendre's formula gives the uniform, absolute bound

\[
\left|v_p(n!)-\frac np\right|\le\frac{2n}{p^2}+R,
\qquad
\sum_{n^s<p\le n^t}\left|v_p(n!)-\frac np\right|\log p
\ll n^{1-s}+K n^t.
\tag{Q12}
\]

There is no extra factor log n in this estimate. To see this explicitly,
write theta(u)=sum_{p<=u} log p. Chebyshev's bound theta(u)<<u and partial
summation give, for A>=2,

\[
\sum_{p>A}\frac{\log p}{p^2}
=-\frac{\theta(A)}{A^2}
+2\int_A^\infty\frac{\theta(u)}{u^3}\,du
\ll\frac1A.
\]

Use A=n^s for the first term of (Q12), and R theta(n^t)<<K n^t
for the second. The larger scale (log A)/A pertains to summing over all
integers, not to this prime sum.

It follows from (Q10)--(Q12) that the mass of residue c on this subband is

\[
\frac{t-s}{m}nL
+O_m\!\left(nK^{-3}((t-s)L+1)+n+n^{1-s}+Kn^t\right).
\tag{Q13}
\]

The endpoints s,t may depend on n. We use (Q13) only inside the retained
bands, where s>=1/(K+1) and t<=1-d.

## 5. Completing the quantitative estimate

Intersect (a,b] with each retained band. If the sum of these intersection
lengths is ell, adding (Q13) over at most K nonempty intersections gives

\[
\frac\ell m nL+O_m(nL/K^3+Kn).
\tag{Q14}
\]

Indeed, the sum of the errors in (Q12) is at most
O(Kn exp(-L/(K+1))+K^2n exp(-dL))=o(n).

Applying (Q10) and (Q12) without a residue condition to all retained bands
shows that their total factorial mass is ell_K nL+O(Kn).
Writing M_omit for the mass of their complement gives

\[
M_{\rm omit}=\log(n!)-\ell_K nL+O(Kn),
\qquad 0\le M_{\rm omit}\ll nL/K,
\tag{Q15}
\]

using (Q3), Stirling's estimate log(n!)=nL+O(n), and K^2<=L.
Also 0<=b-a-ell<=1-ell_K=O(1/K). Adding the omitted part to (Q14),
bounded by (Q15), proves

\[
M_{m,c}(n;a,b)=\frac{b-a}{m}nL+O_m(nL/K).
\]

Since K is comparable, with constants depending on m, with
(L/(log L)^3)^(1/9), and nL-log(n!)=O(n), this is (Q1).

## 6. Review status and limitations

This is a parameter-tracked proposed proof, not an invocation of the
qualitative lemma with moving parameters. The source inequality and its
absolute constants are the central analytic dependency. The finite Fourier
construction is included to expose the dimension and frequency costs.

### Why Proposition 1 rather than the box-counting Proposition 2?

Sander's Proposition 2 (printed p.111, condition (77)) assumes
P<=x^(1/J); the general box estimate at the beginning of printed p.114
is obtained under the same hypothesis. Padding the dimension to J=9
therefore does not cover the full bands with R<=8: their upper endpoints
have 9 beta_R>1, whereas the needed prime prefixes reach n^beta_R.
Those eight bands have a positive fraction of the total logarithmic length,
so discarding them would not prove (Q1). Proposition 1 instead uses
T<=x^(1/j), where j is the smallest nonzero exponent of each frequency.
Keeping this distinction is the reason for the separate Fourier construction.
This does not preclude adapting the proof of Proposition 2.

### Scale, lower bound, and parameter scope

The relative error supplied by (Q1) tends to zero if

\[
\frac{b-a}{L^{-1/9}(\log L)^{1/3}}\longrightarrow\infty
\]

for fixed m. The absolute estimate remains valid for narrower intervals,
but it does not establish an asymptotic main term there.

An absolute error uniform in a,b cannot be o_m(n). Indeed, take
a=1-log(2)/L, b=1 and c=0 modulo m. Every prime in (n/2,n] has valuation
1, so its residue-0 mass is zero for every m>=2. The proposed main term is

\[
\frac{\log2}{mL}\log(n!)\sim\frac{\log2}{m}\,n.
\]

Thus the worst error over intervals and residues is at least a positive
m-dependent multiple of n. This is compatible with an O_m(n) upper bound;
we neither obtain nor rule out such a bound.

The power balance is 9=5+3+1: v_5 contributes K^5, the shortest prefix
in Lambda(T,xH)log T contributes K^3, and the logarithm of the positive
cost contributes one further K. It describes the present estimates, not
a proved ceiling for every refinement of this method. With the old crude
mode count the corresponding balance was K^10(log K)^2 against L,
giving the weaker error n L^(9/10)(log L)^(1/5); the first version's
choice K=L^(1/12) was more conservative still.

The dominant error here is the omitted range of logarithmic length O(1/K),
especially p<=n^(1/(K+1)), not the Fourier discrepancy of size O(nL/K^3).
Better control of that range or sharper exponential-sum and approximation
estimates could change the balance; no optimality claim follows from it.
We keep m fixed. A growing-modulus version requires a separate uniform
accounting of constants and of every hypothesis, not just inspection of (Q8).

No numerical value of the implied constant, no numerical n_0(m), no
optimality of the exponent, and no new result on the remaining k=1,2 branches of
#398 are asserted. A bound with a positive saving can strengthen the
presentation of the mass theorem; it does not replace independent review
of that theorem or the novelty check.

Source: J. W. Sander, *On the order of prime powers dividing* \(\binom{2n}{n}\),
Acta Mathematica 174 (1995), 85--118, Proposition 1, printed pp.109--110;
common parameters p.97 and constants convention p.87.
[DOI](https://doi.org/10.1007/BF02392802).
