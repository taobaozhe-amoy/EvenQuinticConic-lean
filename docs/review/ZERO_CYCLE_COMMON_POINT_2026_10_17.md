# Zero-cycle step: source check and the real common point

Reviewed 2026-10-17. Scope: §6 of
[`EVEN_THETA_CONNECTEDNESS_PROOF.md`](../EVEN_THETA_CONNECTEDNESS_PROOF.md).

**Verdict:** this implication is valid, conditional on the preceding proof of
generic isotropy. This review does not certify that preceding proof, and it is
not a Lean formalization of the zero-cycle theorem.

## Primary-source check

Source: J.-L. Colliot-Thélène and M. Levine,
*Une version du théorème d'Amer et Brumer pour les zéro-cycles*, author revision
of 4 December 2009:
[author PDF](https://www.imo.universite-paris-saclay.fr/~jean-louis.colliot-thelene/CTLevine4dec2009.pdf).
The definition is on printed p. 1; Theorem 3 is on printed p. 5, with its proof
continuing on p. 6.

The paper uses
\[
 I(T/k)=\gcd\{[\kappa(P):k]:P\in T\text{ closed}\},\qquad
 I_{\mathrm{red}}(T/k)=\prod_{\ell\mid I(T/k),\ \ell\text{ prime}}\ell.
\]
Thus “reduced” means squarefree radical of the full index. It does **not**
remove the factors dividing the forms' degree or the characteristic.

Theorem 3 concerns homogeneous forms \(f_0,\ldots,f_r\), not all zero, of
common degree \(d\ge1\), in \(n+1\ge r+2\) variables over a field \(k\).
With independent \(w_1,\ldots,w_r\), it identifies the reduced index of their
common projective zero locus with that of
\[
 f_0+w_1f_1+\cdots+w_rf_r=0
 \quad\text{over }k(w_1,\ldots,w_r).
\]
Smoothness and complete-intersection conditions are absent. Its explicit
corollary equates existence of degree-one zero-cycles. The subsequent remark
warns that rational-point equivalence fails for three quadrics over general
fields.

## Application to this net

Set
\[
 Q_i(z)=z^{\mathsf T}M_i z,\qquad
 \Gamma=V(Q_0,Q_1,Q_2)\subset\mathbb P^4_{\mathbb R},\qquad
 F=\mathbb R(x,y).
\]
There are three forms, so \(r=2\), and five variables, so \(n=4\).
Consequently \(d=2\ge1\) and \(5\ge2+2\). The forms are not all zero:
the generic symmetric form is nondegenerate, because its determinant is the
nonzero polynomial defining the quintic. In characteristic zero, a symmetric
matrix with identically zero quadratic polynomial is itself zero, as follows
by reading its diagonal and off-diagonal coefficients.

A nonzero isotropic vector for \(Q_0+xQ_1+yQ_2\) gives an actual point of its
projective quadric over \(F\). This point is a degree-one closed point. Hence
that quadric has index one. Applying the checked theorem gives
\[
 I_{\mathrm{red}}(\Gamma/\mathbb R)=1,
 \qquad I(\Gamma/\mathbb R)=1.
\]
The second equality follows because a positive integer greater than one has a
prime divisor. The assertion supplies a finite integer linear combination of
closed points of total degree one; it need not initially be an effective cycle.

## Why odd degree suffices over the real field

Here is the separate elementary argument, including the residue-field issue.
For any finite-type scheme \(T/\mathbb R\) and closed point \(P\), choose an
affine neighborhood. Zariski's lemma makes its residue field \(\kappa(P)\) a
finite extension of \(\mathbb R\). Every finite extension of \(\mathbb R\)
embeds over \(\mathbb R\) into its algebraic closure \(\mathbb C\); the tower
law and \([\mathbb C:\mathbb R]=2\) imply
\[
 [\kappa(P):\mathbb R]\in\{1,2\}.
\]
In degree one, the structure map identifies the residue field with
\(\mathbb R\), giving a morphism \(\operatorname{Spec}\mathbb R\to T\).
Thus a degree-one closed point is a real point.

Suppose a zero-cycle
\[
 z=\sum_{j=1}^N m_j[P_j],\qquad m_j\in\mathbb Z,
\]
has odd degree. If no point in its support had degree one, then every degree
would be two and
\[
 \deg z=\sum_{j=1}^N 2m_j=2\sum_{j=1}^N m_j
\]
would be even, a contradiction. This proof allows negative coefficients and
does not assume the cycle is effective. It proves
\[
 \text{odd-degree zero-cycle on }T\quad\Longrightarrow\quad T(\mathbb R)\ne\varnothing.
\]
Taking \(T=\Gamma\) and the degree-one cycle above gives a projective common
real zero. Any representative is a nonzero vector \(P\in\mathbb R^5\)
satisfying all three equations; that is the common-point input needed by the
incidence construction.

No three-form rational-point version of Amer–Brumer, direct specialization
of a moving isotropic vector, or existence of a real point from a degree-two
cycle has been used. The real-field residue-degree argument is the essential
extra step after the zero-cycle theorem.

## Formalization boundary

The source theorem and its Chow-theoretic proof are still external mathematical
inputs. The later Lean incidence theorems take an actual common point as input;
this review verifies a paper-level route to that input. It does not turn the
external theorem or the earlier generic-isotropy argument into a kernel-checked
result.
