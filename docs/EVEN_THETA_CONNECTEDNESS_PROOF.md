# Even theta characteristic and real connectedness

Date: 2026-10-15.

This document records a candidate mathematical argument using the classical
results explicitly listed below. Its unformalized geometric bridges remain
subject to verification, so it is **not a certified complete proof or a
completed Lean formalization**. Passing the repository's
build or axiom audit does not certify the real-geometric, Brauer-theoretic,
quadratic-form, or birational steps of this proof. In particular, the conclusion
below is not being inferred from a Lean lemma that assumes connectedness.

A fresh adversarial review on 2026-10-16 checked the theorem inputs and the
real-sign, Clifford, Pfister, zero-cycle and incidence steps without finding
a fatal error. This is a paper-level review, not a full formal certification;
see [the detailed review and the odd-theta calculation for the user's example](RECHECK_2026_10_16.md).

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

For the alternative definition of a geometrically standard conic bundle using
geometric relative Picard number one, the relative anticanonical model theorem is
the geometric input; see [3, Definition 3.1 and Theorem 3.2]. Over the complex
numbers it gives the quadratic model, and the canonical relative anticanonical
construction descends to \(\mathbb R\) by flat base change and faithfully flat
descent. No conclusion about real rationality is imported from a theorem stated
only over an algebraically closed field.

More explicitly, if relative anticanonical ampleness is not included in the
definition, choose a relatively ample divisor A after complexification. Relative
Picard number one gives -K_X numerically equivalent over S to lambda A. Evaluating
on a smooth conic fiber gives lambda=2/(A.f)>0. Every irreducible component of
each one-dimensional fiber therefore has positive anticanonical degree. The
proper-curve ampleness criterion and openness of fiberwise ampleness give
relative anticanonical ampleness; see Stacks
[0B5Y](https://stacks.math.columbia.edu/tag/0B5Y) and
[0D2S](https://stacks.math.columbia.edu/tag/0D2S). Flatness and relative dimension
one are retained throughout. For descent, define the anticanonical pushforward
and its evaluation over the real field first. Flat base change identifies their
complexifications with the rank-three bundle and surjective evaluation in [3].
Local freeness, surjectivity and the resulting closed immersion descend. The
ideal of that immersion has relative degree -2; the projective-bundle Picard
formula gives the stated real line-valued quadratic form.

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
\(J\).

Apply the same reasoning to the \(\mathcal O(1)\)-valued form \(M\) on the
trivial rank-five bundle. It has rank four along \(C\), and its quotient form
has signature \((2,2)\) on \(J\). The signed-discriminant cover of this
rank-four quotient also splits on \(J\).

We next compare their underlying trace-zero line bundles. Let

\[
K=\operatorname{rad}(M|_C),\qquad W=\mathcal O_C^5/K.
\]

Twisting the resolution by two gives cokernel \(\theta(2)\) for
\(\mathcal O_C^5\to\mathcal O_C(1)^5\). Symmetry identifies this cokernel
with \(K^*\otimes\mathcal O_C(1)\). Therefore

\[
K\simeq\theta^{-1}(-1),\qquad
\det W\simeq\theta(1),\qquad
\det W\otimes\mathcal O_C(-2)\simeq\theta(-1)=\eta.
\]

The last line is the trace-zero line of the rank-four signed-discriminant
cover. The signed discriminant of an even-dimensional form of dimension
\(n\) is \((-1)^{n(n-1)/2}\det\): it is \(-\det\) in rank two and
\(+\det\) in rank four.

After identifying the two trace-zero lines, their square trivializations differ
by a unit of \(\Gamma(C,\mathcal O_C)=\mathbb R\). Up to squares this unit
is either positive or negative. At any point of \(J\), both covers split, so
the ratio is positive and has a real square root. Rescaling the line
identification by that root identifies the square trivializations. Thus the
two covers agree **over \(\mathbb R\)**, not just after complexification.

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
\((-ab,-a\varpi u)\) gives residue \(-ab\). These are exactly the two
signed-discriminant covers compared in §2. Therefore \(\beta-\alpha\) has
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

Suppose a definite real member of the net existed. There are also members of
signature \((3,2)\) near \(J\). A path between these parameter values must
leave the open definite locus at a point of \(C(\mathbb R)\). At such a
boundary point the matrix has rank four, by smoothness of \(C\), and its
rank-four quotient is definite. Its signed discriminant is positive.

By §2 the original discriminant cover splits there. The original rank-two
quotient form is therefore indefinite, so the original conic has real points
on both adjacent nonsingular sides of \(C\). Consequently \(\alpha\)
specializes to zero at nearby definite members of the net. The table says that
\(\beta\) specializes to the nonzero quaternion class at those members,
contradicting \(\alpha=\beta\).

Thus every nonsingular real member is indefinite. To pass from real parameter
values to all orderings of \(F\), take any real closure of \(F\) for a chosen
ordering. If \(q\) were definite there, Sylvester's criterion would give a
finite system of strict polynomial inequalities in \(x,y\), with real
coefficients, that is solvable in this real closed extension. Transfer for real
closed fields gives a solution in \(\mathbb R\). It would be a definite
nonsingular real member, a contradiction. Hence \(q\) is indefinite at every
ordering of \(F\).

This uses real-closed-field transfer for a finite semialgebraic condition; it
does not identify arbitrary function-field orderings with evaluation at real
points.

## 5. The generic five-dimensional form is isotropic

We give the quadratic-form argument, including its dimension and determinant
checks. Let \(k\) have characteristic different from two, let \(q\) be
nondegenerate of dimension five, and write \(d=\det q\) modulo squares. The
six-dimensional form

\[
r=q\perp\langle-d\rangle
\]

has trivial signed discriminant, since
\((-1)^{15}\det(r)=d^2\). Its two even Clifford components are isomorphic
to \(C_0(q)\). By the Albert-form classification and index criterion
[4, Proposition 16.3 and Theorem 16.5], if
\(\operatorname{ind}C_0(q)\le2\), then \(r\) is isotropic. Split off a
hyperbolic plane:

\[
r\simeq\mathbb H\perp\rho.
\]

The four-dimensional remainder has trivial signed discriminant, hence is
similar to a two-fold Pfister form: \(\rho\simeq a\pi\). Adding
\(\langle d\rangle\) and canceling a hyperbolic plane gives

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
index is one. It follows that \(\Gamma\) has a zero-cycle of degree one.
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

On the nonempty open subset of \(\mathbf P^3\) where a minor is nonzero,
the cross product of the two rows gives the unique \(t\). The corresponding
open subset of \(Z\) is therefore isomorphic to this open subset of
\(\mathbf P^3\). Let \(Z_0\) be its irreducible closure. Then \(Z_0\) is
a rational threefold.

The actual incidence-open dominance step is now formalized under the geometric
Jacobian condition; see [the precise statement and remaining gaps](INCIDENCE_DOMINANCE.md).
The paper argument below checks dominance over \(\mathbf P^2\), rather than merely
rationality of some component. Every geometric \(t\) has \(l_t\ne0\).
If \(r_t\) vanished on the plane \(l_t=0\), it would be divisible by
\(l_t\); then \(Q_t\) would have rank at most two, contrary to the
smoothness of the determinant curve. Thus every fiber of \(Z\to\mathbf P^2\)
has dimension one. Since \(\dim Z_0=3\), the dimension-of-fibers inequality
forces \(Z_0\) to dominate the two-dimensional base. The generic conic is
smooth and geometrically integral, so it has a unique component dominating
the base. This identifies the rational component with the required conic
function field.

Finally, hyperbolic reduction preserves the relevant even Clifford Brauer
class. The sign can be checked without convention ambiguity: if the
three-dimensional remainder is \(\langle a,b,c\rangle\), take
\(\mathbb H=\langle1,-1\rangle\). Then

\[
[C_0(\langle1,-1,a,b,c\rangle)]
=(1,-a)+(-ab,-ac)
=(-ab,-ac)
=[C_0(\langle a,b,c\rangle)].
\]

The generic conic of \(Z_0\) therefore has class \(\beta=\alpha\). Smooth
conics over a field are classified by their associated quaternion Brauer
classes, including the split class. Hence the generic conics of \(X\) and
\(Z_0\) are isomorphic over \(F\), and

\[
X\sim_{\mathbb R}Z_0\sim_{\mathbb R}\mathbf P^3.
\]

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
a proper algebraic subset has real dimension strictly less than three and
cannot contain an open subset of the smooth real three-manifold.

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
   space. [Author PDF](https://math.mit.edu/~poonen/papers/Qpoints.pdf).
3. Y. Prokhorov, *The rationality problem for conic bundles*, Definition 3.1
   and Theorem 3.2: the relative anticanonical quadratic model. Its complex
   rationality results do not themselves imply the real conclusion here.
   [Author preprint](https://arxiv.org/pdf/1712.05564).
4. M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of Involutions*,
   Proposition 16.3 and Theorem 16.5, printed pp. 235–236: Albert forms and
   the index/isotropy criterion.
   [University-hosted preprint](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/involutions.pdf).
5. R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of
   Quadratic Forms*, Theorem 31.22 and Corollary 35.29, printed pp. 128 and
   159: the signature local-global theorem and torsion-freeness of
   \(I^{n+1}\) for transcendence degree \(n\) over a real closed field.
   [Author PDF](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf).
6. J.-L. Colliot-Thélène and M. Levine, *Une version du théorème d'Amer et
   Brumer pour les zéro-cycles*, Theorem 3, pp. 5–6 of the 4 December 2009
   author version. [Author PDF](https://www.imo.universite-paris-saclay.fr/~jean-louis.colliot-thelene/CTLevine4dec2009.pdf).
7. Stacks Project, [Tag 01XS](https://stacks.math.columbia.edu/tag/01XS):
   cohomology of projective space.
8. Stacks Project, [Tag 01X0](https://stacks.math.columbia.edu/tag/01X0):
   effective Cartier divisors and the associated line bundles and sections.

This is a proof at the mathematical-paper level, subject to the stated
geometric convention and the cited theorem inputs. It does not report that the
repository has constructed and verified every object and implication above in
Lean. The exact formalization boundary remains recorded separately in
[PROOF_STATUS.md](PROOF_STATUS.md).
