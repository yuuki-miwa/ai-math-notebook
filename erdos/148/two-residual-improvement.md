# Two residuals: improving the five-term exponent to 23/15

Date: 2026-09-08. Private research continuation; no publication or expert
contact is part of this work. No author byline.

Status: a complete derivation from published inputs is given below. The
new algebraic identity, its explicit constant, the divisor switch, and the
rational exponents have been checked exactly. This is an internally
checked research result, not an externally reviewed theorem or a claim of
established priority.

AI use: OpenAI Codex developed the new argument, performed the exploratory
optimization, wrote the proof and verification program, and checked the
sources. Earlier notes and an earlier Claude review were available as
background. Claude did not review this new argument. The finite checks
below are not independent human review and are not the proof of the
asymptotic estimates.

## 1. Result

As before, f_k(m,n) counts nondecreasing positive integer denominators in
a representation of m/n by k unit fractions. Put X=n^2/m. We obtain

\[
 f_5(m,n)\ll_\varepsilon n^\varepsilon X^{23/15}
 \qquad(m,n\in\mathbb N).
 \tag{1}
\]

The published lifting lemma and our existing prefix--tail argument then give

\[
 f_k(m,n)\ll_\varepsilon (kn)^\varepsilon
 \left(\frac{k^{4/3}n^2}{m}\right)^{(23/15)2^{k-5}}
 \quad(k\ge5),
 \tag{2}
\]

and, with gamma=1.264084735... in the earlier normalization,

\[
 F(k)\le f_k(1,1)
 \le\gamma^{(23/120+o(1))2^k}.
 \tag{3}
\]

The changes from our previous result are

\[
 \frac{446}{289}-\frac{23}{15}=\frac{43}{4335}>0,
 \qquad
 \frac{223}{1156}-\frac{23}{120}=\frac{43}{34680}>0.
\]

Thus the gamma coefficient decreases from 0.192906574... to
0.191666666.... The original open growth-order problem remains open.

## 2. Published inputs and notation

The main source is Elsholtz--Planitzer (EP),
[Sums of four and more unit fractions and approximate parametrizations](https://arxiv.org/html/2012.05984).
We use Lemma 1(4)--(6), equations (16), (23)--(26), and Lemma B.
The equation numbering here is that of the checked arXiv v1 text.
The [journal landing page](https://pmc.ncbi.nlm.nih.gov/articles/PMC8248158/)
was inaccessible to the automated browser on this pass, so this is not
a fresh comparison against the journal version.

Besides their defining sets, the counting bounds needed here are only

\[
 f_3(M,N)\ll_\varepsilon N^\varepsilon (N/M)^{2/3},
 \tag{4}
\]

\[
 f_4(M,N)\ll_\varepsilon N^\varepsilon N^{3/2}M^{-3/4},
 \tag{5}
\]

and

\[
 f_4(M,N)\ll_\varepsilon N^\varepsilon
 \big((N/M)^{5/3}+N^{4/3}M^{-2/3}\big).
 \tag{6}
\]

In particular, the previous 28/17 four-term estimate is not needed in
this proof. Equation (4) and (6) originate with Browning--Elsholtz and
are restated in EP's introduction.

## 3. A four-term estimate with a lower bound on the first residual

Let H_4(M,N;V) count the representations

\[
 \frac MN=\frac1{b_1}+\frac1{b_2}+\frac1{b_3}+\frac1{b_4},
 \quad b_1\le b_2\le b_3\le b_4,
 \quad Mb_1-N\ge V>0.
\]

We claim

\[
 \boxed{H_4(M,N;V)\ll_\varepsilon
 N^\varepsilon\frac{N^2}{M^{5/4}V^{1/2}}.}
 \tag{7}
\]

Here V need not be an integer. Values V>3N give an empty set.

### Derivation of (7)

Initially suppose (M,N)=1 and fix the EP pattern
n_i=gcd(b_i,N), writing b_i=n_i t_i. Use their relative gcd parameters
x_J, so t_i is the product of the x_J whose index contains i. Write
d_34=gcd(N/n_3,N/n_4) and d_234=gcd(N/n_2,N/n_3,N/n_4).
All these pattern factors are positive integers.

Define the following integer products:

\[
\begin{aligned}
 P&=z_{234}x_{23}x_{234},\\
 Q&=z_{34}x_{12}x_{123}x_{124}x_{1234},\\
 R&=x_{12}x_{13}x_{24}x_{34}x_{123}x_{124}x_{134}x_{1234},\\
 S&=x_{12}x_{13}x_{14}x_{23}x_{123}x_{124}x_{134}x_{234}x_{1234},\\
 E&=x_{12}x_{123}x_{1234}.
\end{aligned}
\]

Q, R and S are precisely products of defining sets in EP Lemma 1(4),
(5) and (6). Specifying any one of these products specifies the
parameters in its defining set up to a divisor-bound number of choices.
All parameters and all products above have size polynomial in N when
there is a representation; also M<=4N. Consequently the usual repeated
divisor bounds cost only N^epsilon after adjusting epsilon.

EP equation (26), with its pattern factors retained, says

\[
 P^2 Q R E
 \ll\frac{N^6}{M^3 n_1^3 n_2^2 n_3 d_{34}d_{234}^2}.
 \tag{8}
\]

Set v=Mb_1-N. EP equation (16) and the definitions give

\[
 v=n_1d_{234}z_{234},\qquad
 P=\frac{z_{234}}{t_1}S,\qquad
 t_1\le\frac{4N}{Mn_1}.
\]

Substitution into (8) therefore gives

\[
 \begin{aligned}
 QRS^2E
 &\ll\frac{N^6t_1^2}
 {M^3n_1^3n_2^2n_3d_{34}d_{234}^2z_{234}^2}\\
 &\ll\frac{N^8}{M^5v^2n_1^3n_2^2n_3d_{34}}
 \le\frac{N^8}{M^5V^2}.
 \end{aligned}
 \tag{9}
\]

Since E>=1, at least one of Q,R,S is
O(N^2 M^(-5/4) V^(-1/2)): otherwise QRS^2 would exceed (9).
There are O(N^epsilon) completions per value of the small defining-set
product and O(N^epsilon) patterns, with all epsilon factors rescaled.
This proves (7).

There is also an explicit constant version of the algebraic inequality:

\[
 QRS^2E\,M^5v^2n_1^3n_2^2n_3d_{34}\le18432N^8,
 \qquad18432=2\cdot3^2\cdot4^5.
 \tag{10}
\]

The constant follows directly from EP inequalities (23)--(25), rather
than from interpreting an implicit constant in (8).

For general M,N, put d=gcd(M,N). The same representation has residual
v/d with respect to M/d,N/d, and the cutoff becomes V/d. Applying the
reduced estimate gives an extra factor d^(-1/4), which can be discarded.
Thus (7) holds without a coprimality hypothesis.

## 4. Summing a block using the second residual

For the outer five-term representation set

\[
 u=ma_1-n,\qquad N_u=na_1=\frac{n(n+u)}m,\qquad X=\frac{n^2}m.
\]

As in the earlier proof,

\[
 0<u\le4n,\quad u\equiv-n\pmod m,\quad X<N_u\le5X.
 \tag{11}
\]

Fix a block U<u<=2U within this range. If b is the smallest denominator
of the four-term tail, its next residual is

\[
 v=ub-N_u,\quad 0<v\le3N_u,\quad
 u\mid n^2+mv,
 \quad b=\frac{n^2+nu+mv}{mu}.
 \tag{12}
\]

The divisor relation is valid for all m,n, with no coprimality assumption.
For fixed m,n,u,v there is at most one possible b. We may discard the
condition b>=a_1 when taking upper bounds.

For 1<=V<=X, split this block according as v<=V or v>V.

For v<=V, the denominator of the remaining three-term target is N_u b.
Since b=(N_u+v)/u and N_u<=5X, it is O(X^2/U). By (4), the number of
tails for one pair (u,v) is at most

\[
 n^\varepsilon X^{4/3}U^{-2/3}v^{-2/3}.
\]

For a fixed v, (12) gives at most tau(n^2+mv) choices of u. Since
n^2+mv<=2n^2, the divisor bound gives

\[
 \begin{aligned}
 \#\{\text{representations in the block with }v\le V\}
 &\ll_\varepsilon n^\varepsilon X^{4/3}U^{-2/3}
       \sum_{v\le V}v^{-2/3}\\
 &\ll_\varepsilon n^\varepsilon X^{4/3}U^{-2/3}V^{1/3}.
 \end{aligned}
 \tag{13}
\]

For v>V, apply (7) to each four-term tail. There are O(U) possible u's
in the block, so

\[
 \#\{\text{representations in the block with }v>V\}
 \ll_\varepsilon n^\varepsilon X^2 U^{-1/4}V^{-1/2}.
 \tag{14}
\]

Choose

\[
 V=X^{4/5}U^{1/2}.
 \tag{15}
\]

For 1<=U<=X^(1/3), this lies between 1 and X^(29/30)<=X.
Both (13) and (14) now equal, up to the n^epsilon factor,

\[
 X^{8/5}U^{-1/2}.
 \tag{16}
\]

Thus a structured block of four-term counts satisfies

\[
 \boxed{
 \sum_{\substack{U<u\le2U,\ u\le4n\\u\equiv-n\ ({\rm mod}\ m)}}
 f_4(u,N_u)
 \ll_\varepsilon n^\varepsilon X^{8/5}U^{-1/2}
 }
 \tag{17}
\]

for 1<=U<=X^(1/3). A final truncated block causes no change to this
upper bound. The sum itself counts all four-term tails, so it remains
a valid upper bound after dropping the original ordering constraint.

## 5. Three outer ranges

Assume X>=1. Put alpha=2/15 and beta=1/3; both cutoffs lie below 4n.

For 0<u<=X^alpha, (5) and the elementary residue-class sum give

\[
 \sum f_4(u,N_u)
 \ll_\varepsilon n^\varepsilon X^{3/2}
       \left(1+\frac{X^{\alpha/4}}m\right)
 =n^\varepsilon\left(X^{3/2}+\frac{X^{23/15}}m\right).
 \tag{18}
\]

For X^alpha<u<=X^beta, decompose into blocks with ratio 2 and apply (17).
The sum of U^(-1/2) is a decreasing geometric series, so

\[
 \sum f_4(u,N_u)
 \ll_\varepsilon n^\varepsilon X^{8/5-\alpha/2}
 =n^\varepsilon X^{23/15}.
 \tag{19}
\]

For X^beta<u<=4n, use (6) and keep the residue-class spacing m.
The same elementary sum estimates used in the earlier note give

\[
 \begin{aligned}
 \sum f_4(u,N_u)
 &\ll_\varepsilon n^\varepsilon\left(
 X^{5/3-5\beta/3}+\frac{X^{5/3-2\beta/3}}m
 +X^{4/3-2\beta/3}+\frac{X^{4/3}n^{1/3}}m\right)\\
 &=n^\varepsilon\left(
 2X^{10/9}+\frac{X^{13/9}}m+X^{3/2}m^{-5/6}\right)
 \ll_\varepsilon n^\varepsilon X^{3/2}.
 \end{aligned}
 \tag{20}
\]

The 2 in the middle line is immaterial inside Vinogradov notation.
Combining (18)--(20), using m>=1 and 3/2<23/15, proves (1) for X>=1.
If X<1 and f_5(m,n)>0, then n^2<m<=5n, forcing n<5. The finite number
of remaining (m,n) pairs is absorbed into the constant.

EP Lemma B gives (2), and the prefix--tail argument from the previous
note gives (3) by replacing p with 23/15 and dividing by 8.

## 6. Why the previous obstruction is avoided

The previous divisor-switching attempt applied the three-term bound all
the way to v of order X. Its loss came from that upper end, giving
X^(5/3) U^(-2/3). This note only uses it below (15). Above (15), a
large residual strengthens the four-term defining-set bound through (9).
The two estimates are used on disjoint sets of representations.

At the new outer transition,

\[
 U=X^{2/15},\qquad V=X^{13/15},
\]

both parts cost X^(23/15). The critical exponents now come from

\[
 \frac32+\frac\alpha4=\frac85-\frac\alpha2,
 \qquad\alpha=\frac2{15}.
\]

No unproved average bound has been inserted: the average saving in (13)
is the ordinary divisor bound applied to the exact relation (12).

The next meaningful target is to strengthen one of (13) or (14) near
(U,V)=(X^(2/15),X^(13/15)), or to exploit their remaining shared
arithmetic structure. This is a bottleneck of these particular bounds,
not a lower bound for the true counts.

## 7. Verification and reproducibility

[residual_split_audit.py](../experiments/residual_split_audit.py) uses
only the Python standard library. It checks:

- the three Laurent-monomial identities formally, by comparing integer
  exponent vectors without substituting any sample values;
- all 48,972 nondecreasing four-term representations with
  1<=N<=12 and 1<=M<=4N, including nonreduced inputs;
- the relative-gcd reconstruction, the exact monomial identity behind
  (8)--(9), and the explicit inequality (10) for each representation;
- 50,843 instances of the general-m divisor switch (12);
- every exponent balance in (15)--(20) and the coefficient conversion.

Run `python experiments/residual_split_audit.py` from the repository root.
The algebraic proof above is the justification of the infinite statement;
the enumerations help detect transcription and normalization mistakes.

[four_term_lp.py](../experiments/four_term_lp.py) is the exploratory
linear program that led to (7). It requires NumPy/SciPy and uses 66
permutations of the six published defining sets. Its floating-point
output is not part of the proof, which needs only EP's original three
defining sets Q,R,S and the exact algebra in (9).
