# Even theta characteristic and real connectedness

Last revised: 2026-10-17 (UTC).

This note gives a paper argument under the precise geometric conventions below,
with explicit calculations and identified classical theorem inputs. Six
independent, scoped reviews on 2026-10-17 checked those inputs and supplied
missing details; their dependency map is in
[the theoretical proof review](THEORETICAL_PROOF_REVIEW_2026_10_17.md).
The conclusion is the claim proved by this argument, not a theorem already
certified end to end in Lean. In particular, passing the repository's build or
axiom audit does not certify the unformalized geometric, Brauer, quadratic-form
or real-topological steps. The original problem's final Lean theorem is absent.

The revision explicitly includes the Tor term on restriction, the actual real
cover multiplication, all-ordering transfer, the Albert/Pfister cancellations,
and the identification of function fields using the dominant open's generic
fiber. It does not require irreducibility of the entire incidence scheme.

## Statement and conventions

Let

\[
\pi:X\longrightarrow S=\mathbf P^2_{\mathbb R}
\]

be a geometrically standard conic bundle with smooth projective total space X. We use the usual flat
conic-bundle meaning: its relative anticanonical model is the zero locus of an
\(L\)-valued quadratic form on a rank-three vector bundle \(E\) on \(S\), with
smooth generic conic. Assume its discriminant \(C\subset S\) is a smooth plane
quintic. Let

\[
\widetilde C\longrightarrow C,
\qquad p_*\mathcal O_{\widetilde C}=\mathcal O_C\oplus\eta,
\]

be its actual real discriminant double cover, parametrizing the two geometric
lines in each singular fiber. Multiplication specifies
\(\eta^{\otimes2}\simeq\mathcal O_C\). Put

\[
H=\mathcal O_C(1),\qquad \theta=\eta\otimes H.
\]

By adjunction \(\omega_C\simeq H^{\otimes2}\), so \(\theta\) is a theta
characteristic. Assume that its geometric parity is even:

\[
h^0(C_{\mathbb C},\theta_{\mathbb C})\equiv0\pmod2.
\]

**Claim.** Under these assumptions, \(X\) is \(\mathbb R\)-rational. In
particular, \(X(\mathbb R)\) is nonempty and connected, and

\[
b_0(X(\mathbb R))=1.
\]

The smooth total space is geometrically integral: after base change to
\(\mathbb C\), its irreducible components are open, flatness makes their
images open in the integral base, and the geometrically integral generic conic
permits only one such component.

The theta characteristic is on the discriminant curve; the asserted
connectedness is that of the total space's real locus. Smoothness means geometric
smoothness, not just the absence of singular real points. Evenness concerns the
specific theta characteristic coming from the specified double cover.

The usual conic-bundle hypothesis retains a geometrically smooth generic
conic and flat relative dimension one. These cannot be replaced by relative
Picard number one alone. The direct quadratic-model reference over a field of
characteristic different from two is [9, §2, p. 426]. Alternatively, [3,
Definition 3.1 and Theorem 3.2] gives the construction over an algebraically
closed field of characteristic zero; the canonical construction descends as
follows. No real rationality conclusion is imported from a complex theorem.

If relative anticanonical ampleness is not included in the definition, choose
a relatively ample divisor A after complexification. Geometric relative
Picard number one gives \(-K_X\equiv_S\lambda A\), where a smooth conic fiber
shows \(\lambda=2/(A.f)>0\). Relative ampleness follows from the relative
Kleiman criterion; the precise hypotheses and references are recorded in
[the original-model review](review/ORIGINAL_CONIC_MODEL_2026_10_17.md).

Define \(\mathcal H=\omega_X^{-1}\otimes\pi^*\omega_S\) over \(\mathbb R\),
and \(A=\pi_*\mathcal H\). Flat base change identifies its complexification
with the rank-three pushforward of the geometric anticanonical model. Local
freeness and surjectivity of the evaluation \(\pi^*A\to\mathcal H\) descend,
as does the resulting closed immersion into the quotient-convention
\(\mathbf P_S(A)\). Let \(p:\mathbf P_S(A)\to S\), and let \(\mathcal J\)
be the actual ideal sheaf of this immersion. The sheaf
\(B=p_*(\mathcal J(2))\) is a line bundle: after flat extension to \(\mathbb C\)
this holds and the natural map \(p^*B\to\mathcal J(2)\) is an isomorphism;
both facts descend faithfully flatly. Thus \(\mathcal J=\mathcal O(-2)\otimes p^*B\).
With \(E=A^\vee\) and \(L=B^\vee\), its defining section is the required
\(L\)-valued quadratic form on \(E\). The review gives the precise base-change
and descent references, including Stacks Tags 02KH, 05B2, 02L6 and 01OA.

The discriminant here is the actual effective determinant divisor. Smoothness
of a reduced support alone would not justify the rank calculations below.
This distinction is automatic for the usual smooth ordinary conic bundle,
but must be preserved when translating its definition into formal data.

## 1. Even theta is ineffective on a smooth plane quintic

We first work over \(\mathbb C\). The smooth plane quintic is integral: two
positive-degree plane components would meet and make the curve singular. Suppose
\(s,t\in H^0(C,\theta)\) are linearly independent, and fix the square
isomorphism \(\theta^{\otimes2}\simeq H^{\otimes2}\).

Restriction of homogeneous conics identifies
\(\mathbb C[x_0,x_1,x_2]_2\) with \(H^0(C,H^{\otimes2})\), whereas restriction
of homogeneous quartics is injective. These facts follow from the hypersurface
sequence and the cohomology of line bundles on \(\mathbf P^2\); see [7]. Thus
the sections \(s^2,st,t^2\) lift to conics \(A,B,D\) satisfying the polynomial
identity

\[
AD=B^2.
\]

Here the same square isomorphism is used for all three products. Moreover,
\(A,D\) are nonzero and are not proportional. Indeed, proportionality would
give \(s^2=c t^2\) at the generic point, and a square root of \(c\) in
\(\mathbb C\) would make \(s,t\) proportional.

Unique factorization now gives linear forms \(a,b\) and a nonzero constant
\(c\) such that

\[
A=ca^2,\qquad B=cab,\qquad D=cb^2.
\]

For completeness, remove a greatest common divisor from \(A,D\). Their
remaining coprime factors have even valuations at every irreducible polynomial,
so they are squares up to units. The degree-two condition leaves either a common
factor of degree two and constant residual squares, which would make \(A,D\)
proportional, or a constant common factor and squares of linear forms. Signs of
the linear forms absorb the choice in \(B\).

The actual section identity \(s^2=c(a|_C)^2\) gives equality of zero divisors

\[
2\operatorname{div}_{\theta}(s)
=2\operatorname{div}_{H}(a|_C).
\]

Canceling two in the free abelian group of divisors, and using the
section-divisor correspondence [8], proves \(\theta\simeq H\). Consequently
\(h^0(C,\theta)=h^0(C,H)=3\). This cancellation takes place in the divisor
group, **not** in the Picard group, which has the relevant two-torsion.

We have proved that \(h^0(\theta)\ge2\) forces \(h^0(\theta)=3\). Hence
evenness implies \(h^0(\theta)=0\). Field base change gives the same vanishing
for the actual real line bundle.

Beauville's symmetric-resolution theorem [1, Proposition 4.2(a)] now gives,
directly over \(\mathbb R\), a symmetric matrix of linear forms

\[
M(t)=t_0M_0+t_1M_1+t_2M_2
\]

of size five, with determinant defining \(C\), and a resolution

\[
0\longrightarrow\mathcal O(-2)^5
\xrightarrow{M}\mathcal O(-1)^5
\longrightarrow i_*\theta\longrightarrow0.
\]

The real field is permitted by [1, §0.3 and §2]; this is not an assertion that an
arbitrarily selected complex symmetric matrix descends. Let \(q\) be the
nondegenerate five-dimensional generic quadratic form over
\(F=\mathbb R(S)=\mathbb R(x,y)\), obtained by trivializing \(\mathcal O(1)\)
on an affine chart.

## 2. The actual real covers agree, including their signs

The smooth odd-degree real plane curve \(C\) has a pseudoline component
\(J\subset C(\mathbb R)\). One way to see this is that its mod-two homology
class in \(\mathbf {RP}^2\) is the nonzero class: an odd number of its circle
components must be noncontractible. Two disjoint noncontractible circles cannot
occur in \(\mathbf {RP}^2\). The real line bundle \(H|_J\) is nonorientable.

For the original rank-three quadratic model, the determinant is a section of
\((\det E)^{-2}\otimes L^3\), so

\[
\mathcal O_S(C)\simeq(\det E)^{-2}\otimes L^3.
\]

Write \(\det E=\mathcal O(e)\) and \(L=\mathcal O(m)\), using
\(\operatorname{Pic}(\mathbf P^2_{\mathbb R})=\mathbb Z\). The determinant
identity gives \(3m-2e=5\), so \(m\) is odd. Thus \(L|_J\) is
nonorientable. Smoothness of the determinant curve implies that the quadratic
form has rank exactly two along \(C\).

Transport a trivialization of \(L\) around \(J\). It returns with negative
sign. The quotient by the radical has constant inertia during this transport,
whereas the endpoint form is congruent to the negative of the starting form.
Thus its positive and negative indices agree. Its signature is \((1,1)\).
The original discriminant cover therefore splits over every real point of
\(J\). This is pointwise splitting; it does not assert that the double cover
is topologically trivial over the entire circle.

Apply the same reasoning to the \(\mathcal O(1)\)-valued form \(M\) on the
trivial rank-five bundle. It has rank four along \(C\), and its quotient form
has signature \((2,2)\) on \(J\). The signed-discriminant cover of this
rank-four quotient also splits on \(J\).

We next compare their underlying trace-zero line bundles. Let

\[
K=\operatorname{rad}(M|_C),\qquad W=\mathcal O_C^5/K.
\]

Twist the resolution by two and restrict to \(C\). The full exact sequence is

\[
0\longrightarrow\operatorname{Tor}_1^{\mathcal O_S}
(i_*\theta(2),\mathcal O_C)\longrightarrow\mathcal O_C^5
\xrightarrow{M|_C}H^{\oplus5}\longrightarrow\theta(2)\longrightarrow0.
\]

The hypersurface sequence for \(C\), tensoring with \(i_*\theta(2)\), has
zero multiplication by its defining equation. Consequently its Tor term is
\(\theta(2)\otimes\mathcal O_C(-5)=\theta(-3)\). This gives
\(K=\theta(-3)=\theta^{-1}(-1)\), consistently with the symmetric-map
identification \(\operatorname{coker}(M|_C)=K^*\otimes H\). Hence

\[
K\simeq\theta^{-1}(-1),\qquad
\det W\simeq\theta(1),\qquad
\det W\otimes H^{-2}\simeq\theta(-1)=\eta.
\]

The last line is the trace-zero line of the rank-four signed-discriminant
cover. The signed discriminant of an even-dimensional form of dimension
\(n\) is \((-1)^{n(n-1)/2}\det\): it is \(-\det\) in rank two and
\(+\det\) in rank four.

More explicitly, for a nondegenerate rank-\(2r\) form on \(V\) valued in
\(N\), the discriminant line is \(D=\det V\otimes N^{-r}\), with square
pairing locally equal to \((-1)^{(2r)(2r-1)/2}\det B\). A frame change \(A\)
and value-line frame change \(u\) multiply its generator by \(\det(A)u^{-r}\),
which verifies the gluing of \(\mathcal O\oplus D\) and its multiplication.
For a binary form \(as^2+2bst+ct^2\), choose a local basis with \(a\) a unit.
Since \(a\) is a unit, its isotropic lines all lie in the chart \(t\ne0\).
The actual cover has coordinate \(z=a(s/t)+b\) satisfying
\(z^2=b^2-ac\). Thus it is the signed-discriminant algebra, with its actual
square pairing, not only a line bundle of order two. Under the above frame
changes its generator satisfies \(z^{\prime}=\det(A)u^{-1}z\), as follows
by substituting the change of slope into the binary equation; the full
calculation is in the linked review.

Choose an isomorphism \(f_0:\eta\to D_4\) of the two real trace-zero lines.
If their multiplications are \(\mu_0,\mu_4\), then
\(\mu_4\circ f_0^{\otimes2}=\lambda\mu_0\) for a global unit
\(\lambda\in\Gamma(C,\mathcal O_C)^*=\mathbb R^*\).
At a point of \(J\), both actual quadratic algebras split, so both square
values on nonzero generators are positive. Therefore \(\lambda>0\).
The map \(f=\lambda^{-1/2}f_0\) respects multiplication, proving that the two
actual covers agree over \(\mathbb R\). The complete line-bundle and endpoint
inertia calculations are in
[the theta and real-cover review](review/THETA_AND_REAL_COVERS_2026_10_17.md).

## 3. The Brauer classes agree

Let \(\alpha\in\operatorname{Br}(F)[2]\) be the class of the original
generic conic, and let \(\beta=[C_0(q)]\). Both are unramified away from
\(C\). This can be checked in local trivializations of their quadratic
bundles; their nondegenerate forms give Azumaya even Clifford algebras off the
determinant divisor. In odd rank the Brauer class is unchanged by scaling the
form, so the \(\mathcal O(1)\)-valued presentation introduces no extra
ramification at an affine-chart boundary.

The signs in their residues are important. For a diagonal rank-five form,
the quaternion-symbol formula is

\[
[C_0(\langle a,b,c,d,e\rangle)]
=(-ab,-ac)+(abcd,abce).
\]

At a simple degeneration \(e=\varpi u\), with the other entries units, its
residue is the square class of \(abcd\). For a rank-three form
\(\langle a,b,\varpi u\rangle\), the formula
\((-ab,-a\varpi u)\) gives residue \(-ab\). These residue calculations use the tame symbol formula in [11, p. 2].
They are exactly the two signed-discriminant covers compared in §2. Therefore \(\beta-\alpha\) has
zero residue at every prime divisor of \(S\).

Brauer purity and \(\operatorname{Br}(\mathbf P^2_{\mathbb R})
\simeq\operatorname{Br}(\mathbb R)\), in [2, Theorem 6.8.3 and Proposition
6.9.9], give

\[
\beta-\alpha\in\operatorname{Br}(\mathbb R).
\]

Near any point of \(J\), the original form's rank-two indefinite block remains
indefinite. Thus a nearby nonsingular real conic has a real point and its Brauer
class specializes to zero. The rank-five form nearby has signature \((3,2)\)
or \((2,3)\), and its even Clifford class is also zero. Evaluating the constant
difference there proves

\[
\boxed{\beta=\alpha},\qquad \operatorname{ind} C_0(q)\le2.
\]

Here equality of function-field classes gives equality on their common
unramified open, since the Brauer group of a regular integral scheme injects
into the Brauer group of its function field. Thus this specialization does
not assume an evaluation operation on an arbitrarily ramified class.

## 4. The five-dimensional form is indefinite at every ordering

The displayed Clifford formula over \(\mathbb R\) gives the following table.
Changing all signs does not change the class.

| Signature up to sign | Even Clifford Brauer class |
| --- | --- |
| \((3,2)\) | \(0\) |
| \((4,1)\) | Hamilton quaternion class |
| \((5,0)\) | Hamilton quaternion class |

Suppose the open locus \(D\subset\mathbf {RP}^2\) of definite matrices
were nonempty. It is proper, since there are \((3,2)\) or \((2,3)\) members
near \(J\). Connectedness of \(\mathbf {RP}^2\) gives a boundary point \(b\).
Use a single local trivialization of \(\mathcal O(1)\) near \(b\). Along a
subsequence of definite matrices tending to \(b\), their signs are the same;
the limit is positive or negative semidefinite. It must be singular, since
nonsingular inertia is locally constant. Smoothness of \(C\) gives rank four,
so its quotient is definite and has positive signed determinant.

By §2 the original discriminant cover splits at \(b\). Its rank-two quotient
is therefore indefinite, and this indefinite block persists in a neighborhood.
At nonsingular real points there the original conic has a real point and
\(\alpha\) evaluates to zero. Points of \(D\) occur arbitrarily near \(b\),
and at those points the table gives the nonzero Hamilton class for \(\beta\).
This contradicts \(\alpha=\beta\) on the common unramified open. This argument
requires neither a transverse path nor a globally chosen sign for the net.

Thus every nonsingular real member is indefinite. To pass from real parameter
values to all orderings of \(F\), take any real closure of \(F\) for a chosen
ordering. If \(q\) were definite there, Sylvester's criterion would give a
finite system of strict polynomial inequalities in \(x,y\), with real
coefficients, that is solvable in this real closed extension. Model completeness for real
closed fields [10, Theorem 7.14 and Corollary 7.15] gives a solution in \(\mathbb R\). It would be a definite
nonsingular real member, a contradiction. Hence \(q\) is indefinite at every
ordering of \(F\).

This uses real-closed-field transfer for a finite semialgebraic condition; it
does not identify arbitrary function-field orderings with evaluation at real
points.

## 5. The generic five-dimensional form is isotropic

We give the quadratic-form argument, including its dimension and determinant
checks. Let \(k\) have characteristic different from two, let \(q\) be
nondegenerate of dimension five. Choose a diagonalization and put
\(d=a_1a_2a_3a_4a_5\in k^*\), an actual determinant representative. The
six-dimensional form

\[
r=q\perp\langle-d\rangle
\]

has trivial signed discriminant, since
\((-1)^{15}\det(r)=d^2\). To identify its Clifford components, use generators \(e_i^2=a_i\),
\(f^2=-d\), and set \(w=e_1e_2e_3e_4e_5f\). Then \(w^2=d^2\), \(w\) is
central in the even algebra, and its monomial basis gives

\[
C_0(r)=C_0(q)\oplus C_0(q)w
\simeq C_0(q)\otimes k[T]/(T^2-d^2)\simeq C_0(q)\times C_0(q).
\]

The last map sends \(a+bw\) to \((a+db,a-db)\), so both components really
are the original algebra. By the Albert-form classification and index criterion
[4, Proposition 16.3 and Theorem 16.5], if
\(\operatorname{ind}C_0(q)\le2\), then \(r\) is isotropic. Split off a
hyperbolic plane:

\[
r\simeq\mathbb H\perp\rho.
\]

The four-dimensional remainder has square determinant. Write it as
\(\rho=\langle a,b,c,e\rangle\). The ratio \(e/(bc/a)=abce/(bc)^2\) is a square,
so rescaling its last coordinate gives
\(\rho\simeq a\langle1,b/a\rangle\otimes\langle1,c/a\rangle=a\pi\).
Adding \(\langle d\rangle\) and canceling the resulting common hyperbolic
plane by Witt cancellation [5, Theorem 8.4, pp. 48–49] gives

\[
q\simeq a\pi\perp\langle d\rangle.
\]

Because \(\pi\) represents \(1\), this form is a subform of

\[
\Phi=a\pi\otimes\langle1,d/a\rangle
=a\pi\perp d\pi,
\]

which is similar to a three-fold Pfister form. After extension to a real
closure at any ordering, a Pfister form is either hyperbolic or definite.
If \(q\) is indefinite everywhere,
the containing form \(\Phi\) cannot be definite at any ordering. Its signature
therefore vanishes at every ordering.

Now specialize to \(k=\mathbb R(x,y)\). Pfister's local-global theorem
[5, Theorem 31.22] says that the Witt class of \(\Phi\) is torsion. It lies
in \(I^3(k)\), whose torsion subgroup is zero by [5, Corollary 35.29], applied
to transcendence degree two over the real closed field \(\mathbb R\).
This uses torsion-freeness, not the false assertion \(I^3(k)=0\).
Therefore \(\Phi\) is hyperbolic. Its four-dimensional totally isotropic
subspace intersects the five-dimensional subspace underlying \(q\)
nontrivially, since \(4+5>8\). Thus \(q\) is isotropic over \(F\).

Both hypotheses of this argument were established above: the Clifford index
bound comes from the actual generic conic, and indefiniteness holds at every
ordering, not just every real specialization.

## 6. A real common zero of the three quadrics

Write \(Q_i(z)=z^tM_i z\) and let

\[
\Gamma=V(Q_0,Q_1,Q_2)\subset\mathbf P^4_{\mathbb R}.
\]

Use Colliot-Thélène--Levine [6, Theorem 3] with
\(k=\mathbb R\), \(r=2\), \(d=2\), and \(n+1=5\). The theorem's
variable-count hypothesis is \(n+1\ge r+2\), which here reads \(5\ge4\).
It asserts equality of the reduced indices of the common zero scheme and
the generic hypersurface

\[
Q_0+xQ_1+yQ_2=0
\quad\text{over }\mathbb R(x,y).
\]

No smoothness or complete-intersection hypothesis for \(\Gamma\) is required
by this theorem. The generic hypersurface has a rational point by §5, so its
index is one. In [6, p. 1], the reduced index is the product of the distinct
prime divisors of the full index; it does not discard the prime two. Thus
\(I_{\rm red}(\Gamma)=1\) implies \(I(\Gamma)=1\), so \(\Gamma\) has a
zero-cycle of degree one.
Every closed point over \(\mathbb R\) has degree one or two; if all degrees
were two, no integral linear combination could have degree one. Therefore

\[
\Gamma(\mathbb R)\ne\varnothing.
\]

This is the zero-cycle theorem for three forms. The stronger rational-point
version of the classical two-form Amer--Brumer theorem is not being invoked
for three forms over an arbitrary field.

## 7. An explicit rational incidence model

Choose \(P\in\Gamma(\mathbb R)\) and real coordinates with
\(P=[1:0:0:0:0]\). Write

\[
Q_i(x_0,y)=2x_0l_i(y)+r_i(y),\qquad y\in\mathbb R^4,
\]

where \(l_i\) is linear and \(r_i\) is quadratic. The three \(l_i\) are
independent. Otherwise some nonzero geometric parameter \(t\) would give
\(M(t)P=0\). If \(M(t)\) has rank at most three, its adjugate vanishes and
the determinant curve is singular. If it has rank four, its adjugate equals
\(cPP^t\), and

\[
\frac{\partial\det M}{\partial t_i}(t)
=\operatorname{tr}(\operatorname{adj}(M(t))M_i)
=cQ_i(P)=0.
\]

Again the determinant curve is singular. Both cases contradict smoothness.

Consider the incidence variety

\[
Z=\left\{(t,y)\in\mathbf P^2\times\mathbf P^3:
\sum_i t_i l_i(y)=0,\quad\sum_i t_i r_i(y)=0\right\}.
\]

Its generic fiber is the plane conic obtained by hyperbolic reduction of
\(q\) at \(P\): the isotropic line \(P\) is divided out of its orthogonal
complement. In the displayed coordinates this quotient is exactly
\(l_t(y)=r_t(y)=0\).

The two rows \((l_0,l_1,l_2)\) and \((r_0,r_1,r_2)\) have a nonzero minor
as polynomials in \(y\). If all minors were identically zero, choose
coordinates \(l_i=y_i\). The identities \(y_i r_j=y_j r_i\), unique
factorization, and the pairwise coprimality of the variables force
\(r_i=h y_i\) for a single linear form \(h\). Every member would then factor:

\[
Q_t=l_t(2x_0+h),
\]

contradicting the nonzero determinant of the generic matrix.

On the nonempty open subset of \(\mathbf P^3\) where a fixed minor is
nonzero, the cross product of the two rows gives the unique parameter \(t\).
The equations solve for that parameter over the coordinate ring, so the
corresponding actual open \(U\subset Z\) is isomorphic to this open of
\(\mathbf P^3\). In particular \(U\) is integral and rational of dimension three.
We may take \(Z\) with its reduced structure; the graph open is already reduced.

The actual projection \(U\to S\) is dominant. Here is a paper proof independent
of the Lean endpoint. At every geometric parameter \(t\), independence of the
\(l_i\) gives \(l_t\ne0\). If \(r_t\) vanished on \(l_t=0\), it would be
divisible by \(l_t\), making \(Q_t=l_t(2x_0+h_t)\) have rank at most two.
That contradicts the geometric Jacobian condition on \(\det M\). Hence every
geometric fiber of \(Z\to S\) has the same underlying support as a nonzero
plane conic, and therefore dimension one. This support statement survives
reducing \(Z\): the reduction is a nilpotent closed immersion and its base
changes preserve the underlying support. The fibers of \(U\to S\) are open in these curves and have
dimension at most one. Give the image closure \(Y\) its reduced induced structure; the reduced
scheme \(U\) maps through it. If \(Y\) had dimension at most one, the dimension-of-fibers inequality would give
\(\dim U\le\dim Y+1\le2\), a contradiction [12, Tag 02JS]. Thus \(Y=S\).
The corresponding actual-open dominance result is also formalized at the
matrix-net inputs; see [INCIDENCE_DOMINANCE.md](INCIDENCE_DOMINANCE.md).

Let \(\eta_S\) be the generic point of \(S\). Nondegeneracy of \(q\) gives
\(\operatorname{rad}(P^\perp)=FP\), so the quotient
\(W=P^\perp/FP\) carries a nondegenerate ternary form \(r\). Each quotient
class has a unique representative with \(x_0=0\); hence it is exactly
\((\ker l_t,r_t|_{\ker l_t})\). Therefore

\[
Z_{\eta_S}=C_r=\{l_t(y)=r_t(y)=0\}\subset\mathbf P^3_F.
\]

This is a smooth geometrically integral conic: a reducible ternary quadratic
form over an algebraic closure has rank at most two. If \(Z\) was reduced
first, the identification is unchanged, since the generic-fiber base change
is localization and \(T^{-1}\sqrt I=\sqrt{T^{-1}I}\).

Dominance implies that \(U_{\eta_S}\) is a nonempty open of \(C_r\). This alone
identifies the function field; irreducibility of all of \(Z\) is unnecessary.
Indeed, on affine charts let \(A\hookrightarrow B\) be the actual parameter
pullback, and \(T=A\setminus\{0\}\). Then

\[
\operatorname{Frac}(T^{-1}B)=\operatorname{Frac}(B),\qquad
F(C_r)=F(U_{\eta_S})=\mathbb R(U)\simeq_{\mathbb R}\mathbb R(u,v,w).
\tag{7.1}
\]

The first equality preserves the actual embedding of \(F=\operatorname{Frac}A\).
An arbitrary abstract field isomorphism would not provide this compatibility.

Splitting a hyperbolic plane at \(P\) gives \(q\simeq\mathbb H\perp r\).
For \(r=\langle a,b,c\rangle\) and \(\mathbb H=\langle1,-1\rangle\), the
Clifford generators give an actual algebra isomorphism

\[
C_0(q)\simeq(1,-a)_F\otimes(-ab,-ac)_F
\simeq M_2(C_0(r)),\qquad [C_0(r)]=\beta=\alpha.
\tag{7.2}
\]

For clarity, the conic attached to \(C_0(r)=(-ab,-ac)\) is \(C_r\) itself.
Writing quaternion generators \(i^2=-ab,j^2=-ac,ij=-ji\), its trace-zero norm
satisfies

\[
\operatorname{Nrd}(cz\,i+by\,j+x\,ij)=abc(ax^2+by^2+cz^2).
\]

This explicitly identifies \(C_r\) with the quaternion's norm-zero conic.
Two quaternion algebras in the same Brauer class have the same division
algebra representative and the same degree, hence are isomorphic. Their
trace-zero norm conics are therefore isomorphic too. Equivalently, use the
fixed-dimension Severi–Brauer classification in [2, §4.5.1, pp. 106–107].
It follows from (7.2) that \(X_{\eta_S}\simeq_F C_r\), and then (7.1) gives

\[
\mathbb R(X)=F(X_{\eta_S})\simeq_F F(C_r)\simeq_{\mathbb R}\mathbb R(u,v,w).
\]

Function-field isomorphism gives real birationality by [12, Tags 0BXN, 0BXP].
The full algebra calculations, localization argument and conic identification
are written out in
[the incidence-to-connectedness review](review/INCIDENCE_TO_CONNECTEDNESS_2026_10_17.md).

## 8. Rationality implies the asserted real connectedness

Here is a direct argument that does not require resolution of indeterminacy.
Choose a birational map
\(f:\mathbf P^3_{\mathbb R}\dashrightarrow X\), and embed the projective
variety \(X\) in projective space. Represent the resulting rational map by
real homogeneous polynomials of the same degree and cancel their greatest
common divisor. Their common zero locus \(B\) has algebraic codimension at
least two. On \(U=\mathbf P^3\setminus B\) they define a morphism into
\(X\), since the equations of \(X\) vanish identically on the dense domain
of the rational map.

The real locus \(U(\mathbb R)\) is nonempty and path-connected. To prove
path-connectedness, take \(a,b\in U(\mathbb R)\). Each projective join
\(\operatorname{Join}(a,B)\) or \(\operatorname{Join}(b,B)\) has dimension
at most \(\dim B+1\le2\), and is therefore a proper closed subset of
\(\mathbf P^3\). Choose a real point \(c\) outside their union and distinct
from \(a,b\); real projective space is Zariski dense, so this is possible.
The real projective lines \(ac\) and \(bc\) avoid \(B\) and give paths in
\(U(\mathbb R)\) from \(a\) to \(c\) and from \(c\) to \(b\).

Thus \(f(U(\mathbb R))\) is nonempty and connected. It contains the real
points of a dense Zariski open subset \(V\subset X\) on which the birational
map is an isomorphism. Because \(X\) is smooth and geometrically integral,
\(V(\mathbb R)\) is Euclidean dense in every component of \(X(\mathbb R)\):
a proper algebraic subset cannot contain an open neighborhood of a smooth
real point. The precise local-density statement is [2, Proposition 3.5.75
and Remark 3.5.76, p. 87], which applies in every real component.

Therefore the closure of the connected set \(f(U(\mathbb R))\) is all of
\(X(\mathbb R)\). A closure of a connected set is connected, proving

\[
\boxed{b_0(X(\mathbb R))=1}.
\]

## External inputs and proof boundary

The decisive cited inputs are the real symmetric resolution, Brauer purity,
the Albert index criterion, the two Witt-ring theorems, and the zero-cycle
theorem. Real-closed-field transfer, the elementary classification of conics
by quaternion algebras, and standard line-bundle cohomology are also used.
The remaining comparisons and incidence arguments are proved in this note;
they are not attributed to a source that only proves complex rationality.

1. A. Beauville, *Determinantal hypersurfaces*, Proposition 4.2(a), with the
   ground-field convention in §0.3 and the symmetric-resolution results in §2.
   [Author preprint](https://arxiv.org/pdf/math/9910030).
2. B. Poonen, *Rational Points on Varieties*, Theorem 6.8.3 and Proposition
   6.9.9, printed pp. 197 and 200: purity and the Brauer group of projective
   space; Proposition 6.6.7(i), p. 188 for injectivity into the function field;
   §4.5.1, pp. 106–107 for conic classification; Proposition 3.5.75 and
   Remark 3.5.76, p. 87 for local real density. [Author PDF](https://math.mit.edu/~poonen/papers/Qpoints.pdf).
3. Y. Prokhorov, *The rationality problem for conic bundles*, Definition 3.1
   and Theorem 3.2: the relative anticanonical quadratic model. Its complex
   rationality results do not themselves imply the real conclusion here.
   [Author preprint](https://arxiv.org/pdf/1712.05564).
4. M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of Involutions*,
   Proposition 16.3 and Theorem 16.5, printed pp. 235–236: Albert forms and
   the index/isotropy criterion.
   [University-hosted preprint](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/involutions.pdf).
5. R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of
   Quadratic Forms*, Theorem 8.4 (Witt cancellation, pp. 48–49),
   Theorem 31.22 and Corollary 35.29, printed pp. 128 and
   159: the signature local-global theorem and torsion-freeness of
   \(I^{n+1}\) for transcendence degree \(n\) over a real closed field.
   [Author PDF](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf).
6. J.-L. Colliot-Thélène and M. Levine, *Une version du théorème d'Amer et
   Brumer pour les zéro-cycles*, Theorem 3, pp. 5–6 of the 4 December 2009
   author version. [Author PDF](https://www.imo.universite-paris-saclay.fr/~jean-louis.colliot-thelene/CTLevine4dec2009.pdf).
7. Stacks Project, Lemma 30.8.1, [Tag 01XT](https://stacks.math.columbia.edu/tag/01XT):
   cohomology of projective space.
8. Stacks Project, [Tag 01X0](https://stacks.math.columbia.edu/tag/01X0):
   effective Cartier divisors and the associated line bundles and sections.

9. S. Frei, L. Ji, S. Sankar, B. Viray, I. Vogt, *Curve classes on conic bundle
   threefolds and applications to rationality*, Algebraic Geometry 11 (2024),
   421–459, §2, especially p. 426: quadratic models and actual discriminant
   covers over nonclosed fields of characteristic different from two.
   [Published article](https://api.algebraicgeometry.nl/Article/20462/2024-3-014.pdf).
10. D. Marker, *Model Theory*, Orsay notes, §7, Theorem 7.14 and
    Corollary 7.15, pp. 43–44: quantifier elimination and model completeness
    for real closed ordered fields.
    [Author notes](https://homepages.math.uic.edu/~marker/orsay/orsay3.pdf).
11. J.-L. Colliot-Thélène, *Une remarque sur un article de Hassett, Pirutka et
    Tschinkel*, author version 13 February 2018, p. 2, residue formula after
    Proposition 1.2: the quaternion tame symbol used in §3.
    [Author PDF](https://www.imo.universite-paris-saclay.fr/~jean-louis.colliot-thelene/HPT%2BSrevisited13Feb18.pdf).
12. Stacks Project, [Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)
    (dimension inequality), [Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN)
    and [Tag 0BXP](https://stacks.math.columbia.edu/tag/0BXP)
    (function fields and birationality).

The six scoped reviews and the complete dependency map are linked in
[THEORETICAL_PROOF_REVIEW_2026_10_17.md](THEORETICAL_PROOF_REVIEW_2026_10_17.md).
This paper argument relies on the stated classical results; it does not report
that every object and implication has been constructed and verified in Lean.
The exact formalization boundary remains in [PROOF_STATUS.md](PROOF_STATUS.md).
