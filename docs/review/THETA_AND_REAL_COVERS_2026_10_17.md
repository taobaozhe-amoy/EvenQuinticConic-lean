# Audit of even theta characteristics and the actual real covers

Date: 2026-10-17. Scope: §§1–2 of `docs/EVEN_THETA_CONNECTEDNESS_PROOF.md`.

**Verdict for this scope:** the two implications survive this review. An even
geometric theta characteristic on a smooth plane quintic is ineffective, and
the real symmetric representation obtained from it has the same actual
signed-discriminant cover as the given conic bundle. The second statement
uses the rank-three quadratic-bundle model in the candidate proof and its
actual discriminant cover, not an arbitrarily chosen two-torsion line bundle.

This is a mathematical review with the details below, not a Lean certification
and not a verdict on the later rationality or connectedness argument. The
restriction-to-the-curve calculation needs its Tor term displayed; the
pseudoline argument gives pointwise splitting, not triviality of the cover
on the whole circle. Neither clarification changes the conclusion in this
scope. A real-congruence uniqueness assertion from a separate passage of
Beauville must not be used.

## 1. Precise setting and the ineffective-theta argument

Write \(i:C\hookrightarrow\mathbf P^2_{\mathbb R}\) for a geometrically smooth
plane quintic and \(H=\mathcal O_C(1)\). For the actual finite étale cover
\(p:\widetilde C\to C\), use the actual trace decomposition

\[
p_*\mathcal O_{\widetilde C}=\mathcal O_C\oplus\eta,
\qquad \mu_0:\eta^{\otimes2}\xrightarrow{\sim}\mathcal O_C.
\]

The splitting is defined over \(\mathbb R\), since \(2\) is invertible. Put
\(\theta=\eta\otimes H\); its square identification with \(\omega_C=H^2\)
is an identification of actual real line bundles. Thus no descent obstruction
for a merely Galois-invariant complex Picard class is involved.

Here is an independent check of the argument over \(\mathbb C\). Smoothness
and Bézout make \(C_{\mathbb C}\) integral. The hypersurface sequence

\[
0\to\mathcal O_{\mathbf P^2}(r-5)\to
\mathcal O_{\mathbf P^2}(r)\to i_*H^r\to0
\]

and \(H^1(\mathbf P^2,\mathcal O(k))=0\) show that restriction is an
isomorphism on sections for \(r=1,2,4\). In particular, it is injective for
quartics. The cohomology input is Stacks, Lemma 30.8.1, [Tag 01XT][S1].

Suppose \(s,t\in H^0(C_{\mathbb C},\theta_{\mathbb C})\) are independent.
Choose one square isomorphism \(\phi:\theta^2\to H^2\), and lift
\(\phi(s^2),\phi(st),\phi(t^2)\) to homogeneous conics \(A,B,D\).
Compatibility of multiplication and injectivity for quartics give
\(AD=B^2\) in the polynomial ring. None of \(A,B,D\) vanishes.
If \(A=cD\), then \((s/t)^2=c\) in the function field. A square root of
\(c\in\mathbb C^*\), together with integrality, makes \(s/t\) constant,
contradicting independence. Thus \(A,D\) are not proportional.

For clarity, let \(g=\gcd(A,D)\), \(A=gA_1\), \(D=gD_1\), with
\(A_1,D_1\) coprime. In a UFD, \(g\mid B\), and
\(A_1D_1=(B/g)^2\). Each of \(A_1,D_1\) is a square up to a unit.
Because \(A,D\) both have degree two, the degree of \(g\) is even.
Degree two would make \(A,D\) proportional, so \(g\) is constant.
Absorbing nonzero complex constants and a sign yields

\[
A=ca^2,\qquad B=cab,\qquad D=cb^2
\]

for linear forms \(a,b\) and \(c\ne0\). Consequently the divisor identity
for the actual sections is

\[
2\operatorname{div}_{\theta}(s)
  =2\operatorname{div}_{H}(a|_C).
\]

The divisor group of a smooth integral curve is free abelian, so the two
divisors are equal. The section-divisor correspondence identifies
\(\theta\simeq H\). This uses cancellation in the divisor group, not
cancellation of two in the Picard group. The correspondence is Stacks,
Lemma 31.15.10, [Tag 01X0][S2]. We obtain \(h^0(\theta)=3\).
Therefore every theta characteristic with at least two sections has exactly
three sections, and even parity forces \(h^0(\theta)=0\).

Flat scalar extension gives
\(H^0(C,\theta)\otimes_{\mathbb R}\mathbb C
\simeq H^0(C_{\mathbb C},\theta_{\mathbb C})\), so the actual real bundle
is ineffective too. This argument makes no base-point-freeness assumption
on \(s,t\).

## 2. What Beauville actually supplies over the real field

Checked Beauville's published author PDF [Bea], at these exact locations:

- §0.3, p. 40: arbitrary ground field.
- Theorem B, pp. 44–45: symmetric resolutions, characteristic different from two.
- Corollary 2.4, pp. 45–46: line-bundle specialization.
- Proposition 4.2(a), p. 49: ineffective-theta specialization.

Apply Corollary 2.4 to \(E=\theta(1)\): a line bundle on this curve is ACM,
\(E^2=H^4\), and \(H^0(E(-1))=0\). Twisting the resulting sequence gives

\[
0\to\mathcal O(-2)^5\xrightarrow M\mathcal O(-1)^5
\to i_*\theta\to0
\tag{1}
\]

with \(M\) symmetric and linear. The construction is over \(\mathbb R\);
no chosen complex matrix needs descent. Only the determinant divisor matters.
If \(\det M=aF\), scaling \(M\) by the real fifth root of \(a^{-1}\)
normalizes the equation.

**Do not import real-congruence uniqueness from §2.3.** Its scalar adjustment
requires a square root. As an independent counterexample, the real
\(1\times1\) matrices \((T)\) and \((-T)\) have the same cokernel but are not
congruent. This does not affect the existence result used above.

## 3. Restriction, Tor, duals, and twists

All calculations in this section are over \(\mathbb R\). Let
\(K=\ker(M|_C:\mathcal O_C^5\to H^5)\).
Every geometric point of \(C\) has matrix rank four: at rank at most three,
all \(4\times4\) cofactors vanish, so every partial derivative of the
determinant vanishes, contrary to geometric smoothness. Constant rank makes
\(K\) a line subbundle and \(W=\mathcal O_C^5/K\) a rank-four bundle.

Twist (1) by two and restrict to \(C\). The complete exact sequence is

\[
0\to\operatorname{Tor}_1^{\mathcal O_{\mathbf P^2}}
  (i_*\theta(2),\mathcal O_C)
\to\mathcal O_C^5\xrightarrow{M|_C}H^5
\to\theta(2)\to0.
\tag{2}
\]

The Tor term is not zero. Tensoring
\(0\to\mathcal O(-5)\xrightarrow F\mathcal O\to i_*\mathcal O_C\to0\)
with \(i_*\theta(2)\), on which \(F\) acts by zero, computes it directly:

\[
\operatorname{Tor}_1(i_*\theta(2),\mathcal O_C)
  \simeq\theta(2)\otimes\mathcal O_C(-5)=\theta(-3).
\]

Thus

\[
K\simeq\theta(-3).
\tag{3}
\]

There is an independent symmetry check. The matrix gives a symmetric map
\(b:V\to V^*\otimes H\), with \(V=\mathcal O_C^5\).
Its image is exactly \(K^\perp=W^*\otimes H\), since it lies there by
symmetry and both are rank-four subbundles. Hence restriction to \(K\)
identifies the cokernel with \(K^*\otimes H\). Combining this with (2),

\[
K^*\otimes H\simeq\theta(2),\qquad
K\simeq\theta^{-1}(-1).
\tag{4}
\]

Equations (3) and (4) agree because \(\theta^2\simeq H^2\).
The determinant sequence for \(0\to K\to V\to W\to0\) gives

\[
\det W\simeq K^{-1}\simeq\theta(1),
\qquad D_4:=\det W\otimes H^{-2}\simeq\theta(-1)\simeq\eta.
\tag{5}
\]

Every isomorphism used here is over the real field. The candidate proof's
final twists are correct; (2) is the missing explanation that prevents
mistaking pullback of (1) for a short exact sequence.

## 4. The trace-zero line and its multiplication

Here is a local construction that fixes the dual and the sign. For a
nondegenerate \(L\)-valued quadratic form \(b\) on a rank-\(2r\) vector
bundle \(U\), set

\[
D(U,b)=\det U\otimes L^{-r}.
\]

The determinant of \(b:U\to U^*\otimes L\) is an invertible pairing
\((\det U)^2\to L^{2r}\). It defines the multiplication pairing

\[
\mu_b:D(U,b)^{\otimes2}\to\mathcal O,
\qquad \mu_b=(-1)^{(2r)(2r-1)/2}\det b.
\tag{6}
\]

The signed-discriminant algebra is
\(\mathcal A_b=\mathcal O\oplus D(U,b)\), with
\((a,x)(a',x')=(aa'+\mu_b(x,x'),ax'+a'x)\).
It is finite étale of degree two. Locally, with an orthogonal frame and
\(b(e_i,e_i)=a_i\ell\), its trace-zero generator is the volume element
\((e_1\wedge\cdots\wedge e_{2r})\otimes\ell^{-r}\) and satisfies

\[
z^2=(-1)^{(2r)(2r-1)/2}\prod_i a_i.
\tag{7}
\]

This also checks the transition functions: a frame change \(A\) and a line
frame change \(\ell'=u\ell\) multiply the generator by
\(\det(A)u^{-r}\), whose square is exactly the change in the coefficient
in (7). In characteristic zero the antisymmetrized Clifford volume element
identifies this line with the trace-zero part of the center of the even
Clifford algebra. The field-level center statement is *The Book of
Involutions*, Theorem 8.2(2)(a), printed p. 88 [KMRT]. Equations (6)–(7)
give the line-valued extension here.

For the original conic bundle, restrict its rank-three form to \(C\) and
quotient by its rank-one radical, giving \(U_2\) and the nondegenerate
\(L|_C\)-valued binary form \(b_2\). The actual two lines in the singular
conic correspond to the isotropic lines in \(U_2\): each component is the
inverse image of one such line under \(E|_C\to U_2\).

Locally write the binary form as \(a x^2+2bxy+c y^2\), with \(a\) a unit.
The two isotropic lines lie in the chart \(y\ne0\) and have coordinate
\(t=x/y\). Their algebra is

\[
\mathcal O[t]/(at^2+2bt+c),\qquad z=at+b,\qquad
z^2=b^2-ac=-\det\begin{pmatrix}a&b\\b&c\end{pmatrix}.
\tag{8}
\]

A nondegenerate binary form has a vector of unit value locally, so these
charts cover \(C\). Formula (8), together with the determinant transition
in (7), identifies the actual component cover with
\(\operatorname{Spec}\mathcal A_{b_2}\). Its trace-zero line is
\(D_2=\det U_2\otimes L^{-1}\), with **negative determinant** multiplication.

For a second verification of the line and its dual, use the lines convention
\(\mathbf P_{\rm lines}(U_2)=\operatorname{Proj}(\operatorname{Sym}U_2^*)\).
The isotropic divisor has ideal
\(\mathcal O(-2)\otimes p^*L^{-1}\), and
\(R^1p_*\mathcal O(-2)=\det U_2\). Pushing the divisor sequence forward
and splitting by the trace recovers \(D_2\). The projective-bundle
cohomology used here is Stacks, Lemma 30.8.4, [Tag 01XX][S3], applied to
its quotient-convention bundle \(U_2^*\).

For the rank-four quotient \(W\) of the symmetric matrix, the sign is
**positive determinant**, and its trace-zero line is exactly \(D_4\) from
(5). The two signs must not be replaced by a common unsigned convention.

## 5. The pseudoline and the balanced-inertia argument

The real locus of a geometrically smooth projective plane curve is a compact
smooth one-manifold. For odd degree its mod-two class in
\(H_1(\mathbf {RP}^2,\mathbf F_2)\) is nonzero: intersect with a transverse
real line; nonreal intersection points occur in conjugate pairs and the
total degree is odd. Equivalently it is the Poincaré dual of
\(w_1(\mathcal O(5)_{\mathbb R})=w_1(H_{\mathbb R})\).
At least one component \(J\) therefore represents the nonzero class.
There cannot be two disjoint such components, since their mod-two
intersection number would be one. The underlying topology is the usual
cohomology ring \(H^*(\mathbf {RP}^2,\mathbf F_2)=\mathbf F_2[a]/(a^3)\);
see Hatcher, Theorem 3.19, printed p. 220 in the linked chapter [Hat].

The restriction of the tautological line or its dual to \(J\) is
nonorientable, since \(a\) evaluates to one on \([J]\). Thus \(H|_J\)
is nonorientable. For the original rank-three model,

\[
\mathcal O(C)=(\det E)^{-2}L^3,
\qquad \det E=\mathcal O(e),\quad L=\mathcal O(m),
\qquad 3m-2e=5.
\]

It follows that \(m\) is odd and \(L|_J\) is nonorientable as well.

The needed topological lemma has a concrete proof. Let \(U\to S^1\) be a
rank-\(2r\) real vector bundle with a nondegenerate form valued in a
nonorientable real line bundle \(N\). Cut the circle at a point, and
trivialize \(U\) and \(N\) on the interval. The form is a continuous path
of invertible symmetric matrices \(B(t)\). If the endpoint transition
of \(U\) is \(A\in\mathrm {GL}_{2r}(\mathbb R)\), and that of \(N\)
is a negative scalar \(\lambda\), then, with a consistent choice of
transition directions,

\[
B(1)=\lambda^{-1}A^{\mathsf T}B(0)A.
\]

Inertia is constant along the interval because no eigenvalue passes through
zero. Congruence preserves inertia and multiplication by a negative scalar
exchanges its two indices. Hence those indices are equal, namely \((r,r)\).
No orientability assumption on \(U\) is used.

Apply this to the two quotient bundles over \(J\). The binary form has
inertia \((1,1)\), and the rank-four form has inertia \((2,2)\). Their
signed determinants are positive, so the fibers of both double covers at
each real point of \(J\) are \(\mathbb R\times\mathbb R\).

**Only fiberwise splitting has been proved.** A double cover can have two
real points over every point of a circle and still be a connected topological
double cover of that circle. No global triviality over \(J\) is needed below.

## 6. Removal of the remaining real constant twist

By (5), choose an actual real line-bundle isomorphism
\(f_0:\eta\xrightarrow{\sim}D_4\). Comparing the two invertible pairings
gives a global unit \(c\) with

\[
\mu_4\circ(f_0\otimes f_0)=c\mu_0.
\tag{9}
\]

Geometric integrality and projectivity give
\(\Gamma(C,\mathcal O_C)=\mathbb R\), so \(c\in\mathbb R^*\).
One can also verify the constants by flat extension to \(\mathbb C\),
where regular functions on the projective integral curve are constant.

Choose any \(P\in J\) and any nonzero \(v\in\eta(P)\). For a real
quadratic algebra \(\mathbb R\oplus\mathbb R v\) with \(v^2=d\ne0\),
splitting is equivalent to \(d>0\). Both cover fibers at \(P\) split, so
both \(\mu_0(v,v)\) and \(\mu_4(f_0v,f_0v)\) are positive. Equation
(9) gives \(c>0\).

Set \(f=c^{-1/2}f_0\). Then \(\mu_4\circ f^{\otimes2}=\mu_0\), and

\[
\mathcal O_C\oplus\eta\longrightarrow\mathcal O_C\oplus D_4,
\qquad (a,v)\longmapsto(a,fv)
\]

is an isomorphism of actual real quadratic algebras, hence of their finite
étale covers. This resolves the multiplication and the sign; an isomorphism
of two-torsion line bundles alone would not suffice. Only one real split
fiber was used to fix the constant twist.

## 7. Review boundary and changes recommended for the candidate proof

The present checks support §§1–2 under their stated quadratic-model input.
For a fully explicit version, include (2), (6), (8), the endpoint matrix
identity in §5, and the rescaling direction in (9). Avoid claiming real
congruence uniqueness from Beauville §2.3, and replace any phrase suggesting
that pointwise splitting trivializes the cover globally along \(J\).

This does not prove the later Brauer equality, isotropy over
\(\mathbb R(x,y)\), common-real-point existence, incidence dominance,
birational identification with the original total space, or connectedness
of that total space. It also does not turn the corresponding unformalized
sheaf and real-topological steps into Lean theorems.

## Primary references checked

[Bea]: https://math.univ-cotedazur.fr/u/beauvill/pubs/det.pdf
[KMRT]: https://webhomes.maths.ed.ac.uk/~v1ranick/papers/involutions.pdf
[Hat]: https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf
[S1]: https://stacks.math.columbia.edu/tag/01XT
[S2]: https://stacks.math.columbia.edu/tag/01X0
[S3]: https://stacks.math.columbia.edu/tag/01XX

- A. Beauville, *Determinantal Hypersurfaces*, Michigan Mathematical Journal
  48 (2000), 39–64: §0.3; Theorem B; Corollary 2.4; Proposition 4.2(a).
  [Author-hosted published article][Bea].
- M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol,
  *The Book of Involutions*, AMS Colloquium Publications 44 (1998):
  Theorem 8.2(2)(a), printed p. 88. [University-hosted book preprint][KMRT].
- A. Hatcher, *Algebraic Topology*, §3.2, Theorem 3.19, printed p. 220
  in the linked author-hosted chapter: projective-space cohomology.
  [Author-hosted chapter][Hat].
- Stacks Project, Lemma 30.8.1 [01XT][S1], Lemma 31.15.10 [01X0][S2],
  and Lemma 30.8.4 [01XX][S3].
