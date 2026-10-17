# Audit of the Brauer comparison and the ordering argument

Date: 2026-10-17. Scope: Sections 3–4 of
`docs/EVEN_THETA_CONNECTEDNESS_PROOF.md`.

## Verdict and dependency boundary

I did not find a fatal mathematical error in these two sections. Their
conclusions follow from the actual hypotheses listed below. This is an
independent paper-level check, not a Lean certification of Clifford algebras,
Brauer purity, real topology, or transfer.

The decisive input retained from Section 2 is **an isomorphism over the real
field of the actual discriminant double covers, including their square
trivializations**. Equality of their complexifications, equality of their
underlying two-torsion line bundles, or parity alone cannot replace this input.
This audit does not independently certify the construction of that isomorphism
from the symmetric resolution.

The other inputs are the actual rank-three line-valued quadratic model of the
original conic bundle; the real symmetric rank-five linear matrix; the same
smooth, reduced determinant divisor for both; and a real point of the
pseudoline where the rank-two and rank-four quotient signatures are respectively
(1,1) and (2,2). All real specializations used below are at nonsingular members,
not at a point where the Brauer classes are ramified.

## 1. Direct check of the Clifford formula

Fix the convention that a Clifford generator attached to a diagonal entry a
satisfies e²=a. Let q=⟨a,b,c,d,e⟩ be nondegenerate over a field of characteristic
other than two, and write e₁,…,e₅ for its anticommuting generators. Inside C₀(q),
set

\[
i=e_1e_2,\quad j=e_1e_3,\quad
u=e_1e_2e_3e_4,\quad v=e_1e_2e_3e_5.
\]

Then

\[
i^2=-ab,\quad j^2=-ac,\quad ij=-ji,
\qquad u^2=abcd,\quad v^2=abce,\quad uv=-vu.
\]

Each of u,v commutes with each of i,j. For example, moving two monomials past
one another gives sign (-1)^(rs−s₀), where r,s are their lengths and s₀ is the
number of common generators. Here the signs are +1 between the two pairs and
−1 within each pair. Their four exponent vectors are independent in the
four-dimensional even-weight subspace of (Z/2)^5: the fourth and fifth
coordinates first determine the exponents of u and v, and the second and third
then determine those of i and j. Their sixteen products therefore give the
sixteen independent even Clifford monomials, up to nonzero scalars. This proves
an algebra isomorphism, not merely an analogy of invariants:

\[
C_0(q)\simeq(-ab,-ac)\otimes(abcd,abce).
\]

Thus the displayed Brauer formula in Section 3 is correct. In rank three the
same first pair gives C₀(⟨a,b,c⟩)≃(−ab,−ac). The structural facts that odd-rank
even Clifford algebras are central simple, and that the center in even rank is
the signed-discriminant algebra, are stated in Knus–Merkurjev–Rost–Tignol,
*The Book of Involutions*, §8.A, Theorem 8.2, printed p. 88
([author text](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/involutions.pdf),
PDF page 106). The explicit generators above independently fix the signs used
here.

Replacing all five coefficients by λ times themselves multiplies the first two
symbol entries by λ² and the last two by λ⁴. These are squares, so the Brauer
class is unchanged for every λ≠0. Rank three has the same property. In
particular, replacing a local trivialization of the value line, even by a
rational factor having a zero or pole along the omitted projective line, does
not change the generic Brauer class.

## 2. Local residues, including the projective boundary

At the generic point of the smooth determinant curve, work over its local DVR.
Because the determinant vanishes to order exactly one and the reduced matrix
has corank one, elementary orthogonal elimination over this DVR gives diagonal
presentations

\[
q_5=\langle a,b,c,d,\varpi u\rangle,
\qquad q_3=\langle A,B,\varpi U\rangle,
\]

with all displayed lowercase and uppercase coefficients other than ϖ units.
This diagonalization is available over a local ring with 2 invertible: a
nonzero residual quadratic form represents a nonzero element of the residue
field, yielding a unit pivot; split off that line and repeat. The remaining
one-dimensional entry has valuation one by the determinant condition.

For a quaternion symbol, the residue square class is

\[
\partial_v(s,t)=
(-1)^{v(s)v(t)}\overline{s^{v(t)}/t^{v(s)}}.
\]

A direct reference for this formula is Colliot-Thélène, *Introduction to work
of Hassett–Pirutka–Tschinkel and Schreieder*, the formula immediately after
Proposition 1.2, printed p. 2 of the 14 February 2018 author version
([PDF](https://www.imo.universite-paris-saclay.fr/~jean-louis.colliot-thelene/HPT%2BSrevisited13Feb18.pdf)).
Only this residue formula is needed here; no surjectivity assertion for an
arbitrary DVR residue map is used.

Applying it to the directly checked symbols gives

\[
\partial_C\beta=\overline{abcd},\qquad
\partial_C\alpha=\overline{-AB}.
\]

These are respectively +det of the rank-four quotient and −det of the
rank-two quotient. Both are the signed discriminants
(−1)^{n(n−1)/2}det in their respective even dimensions. For the rank-two form,
its two isotropic lines are defined over the square-root algebra of −AB; this
also checks directly that its residue is the original lines-in-the-singular-
fiber cover. The hypothesized isomorphism of the actual covers identifies
these two residue classes over R(C).

At any other prime divisor D of the projective base, choose local
trivializations of both the vector bundle and its value line at the generic
point of D. The matrices are unimodular there. Orthogonal elimination now
makes every diagonal coefficient a unit; the displayed quaternion symbols
therefore have zero residue. This works equally at the affine-chart boundary.
A calculation using a single affine representative without its value-line
rescaling would not justify this step; the scaling calculation in §1 does.

## 3. Purity and the constant difference

The exact references in Poonen, *Rational Points on Varieties*, are:

- Theorem 6.8.3, printed p. 197: for a regular integral noetherian scheme,
  the kernel of all codimension-one Brauer residues is its Brauer group.
- Proposition 6.9.9, printed p. 200: the structural map induces
  Br(k)≃Br(Pⁿ_k).
- Proposition 6.6.7(i), printed p. 188: the Brauer group of a regular integral
  noetherian scheme injects into that of its function field.

These statements were read in the
[author PDF](https://math.mit.edu/~poonen/papers/Qpoints.pdf), PDF pages
211, 214, and 202 respectively. The characteristic-related qualifications in
the purity theorem cause no restriction over R. The same injection applies to
the regular open U=P²_R∖C. Consequently the residue calculation gives a unique
constant γ∈Br(R) whose pullback is β−α, and equality can be evaluated on U.

Here is the needed specialization argument explicitly. Take a real point s of
the pseudoline. Trivialize both quadratic bundles in a small real neighborhood.
The rank-two quotient of the original form has one positive and one negative
eigenvalue. These eigenvalues remain of opposite signs nearby, so every
nearby nonsingular rank-three form is isotropic and its conic class is zero.
Likewise the rank-five matrix has two positive and two negative eigenvalues
bounded away from zero at s. At any sufficiently close nonsingular point,
its signature is (3,2) or (2,3). There exist such points because C is a smooth
real curve in a real surface.

At these points the even Clifford class is zero, as checked next. Local
nondegenerate Clifford algebras give classes on neighborhoods in U, and agree
with the restrictions of α and β by the generic-point injection. Their
specializations are therefore precisely the field-valued Clifford classes
being computed, rather than a proposed evaluation of ramified classes at s.
At one such nearby real point t,

\[
\gamma=\beta(t)-\alpha(t)=0.
\]

It follows that β=α and ind(C₀(q))≤2, since α is represented by a quaternion
algebra. This does not presume a real point of the generic conic.

## 4. Real signatures and exclusion of definite members

Over a real closed field, a quaternion symbol (s,t) is Hamilton precisely when
both entries are negative. Normalize diagonal coefficients to ±1 and permute
them as follows; H denotes the nonzero Hamilton class:

| Signature | Diagonal representative | First symbol | Second symbol | Sum |
| --- | --- | --- | --- | --- |
| (5,0) | (1,1,1,1,1) | (−1,−1)=H | (1,1)=0 | H |
| (4,1) | (1,1,1,1,−1) | (−1,−1)=H | (1,−1)=0 | H |
| (3,2) | (1,1,1,−1,−1) | (−1,−1)=H | (−1,−1)=H | 0 |

Negating the form does not change its class by §1, covering the other
signatures. This verifies the table without importing a potentially different
Clifford-sign convention.

Suppose a definite member exists. The definite locus is an open subset of
RP², is nonempty by supposition, and is proper because there are indefinite
members near the pseudoline. RP² is connected, hence this locus has a
nonempty boundary. Choose a boundary point b. In a local trivialization, a
sequence of definite matrices converging to M(b) has a subsequence of one
fixed sign. Thus M(b) is positive or negative semidefinite. It cannot be
nonsingular, because definiteness is open, so b lies on C. Smoothness of the
determinant curve forces rank exactly four; therefore its rank-four quotient
is definite and has positive signed discriminant.

The actual cover agreement now implies that the original rank-two quotient
at b is split, hence indefinite. This indefinite block persists throughout a
small neighborhood of b, so α vanishes at every nonsingular real point there.
There are definite members arbitrarily close to b by the definition of a
boundary point, and all definite members are nonsingular. At any such point
β=H by the table, contradicting β=α. Thus there are no definite nonsingular
real members.

This boundary formulation avoids two presentation issues in a path argument:
there is no global choice of sign for an O(1)-valued matrix on RP², and no
transversality of a chosen path to C is needed. Local trivializations and a
subsequence of one sign suffice. The original path argument can also be made
valid by trivializing along its parameter interval.

## 5. Passing to all orderings really uses transfer with real parameters

Use the fixed affine matrix A(x,y)=M₀+xM₁+yM₂ representing the generic form.
Let ≺ be any ordering of F=R(x,y), and choose its compatible real closure F_≺.
The restriction of ≺ to R is its unique ordering, so R⊂F_≺ is an inclusion of
real closed ordered fields.

Write Δ_j(x,y) for the determinant of the leading j×j principal submatrix of
A, for j=1,…,5. These are polynomials with real coefficients. If q is positive
definite over F_≺, Sylvester's criterion gives

\[
\bigwedge_{j=1}^{5}\Delta_j(x,y)>0.
\]

If it is negative definite, the corresponding conjunction is
(−1)^jΔ_j(x,y)>0. Each is a finite existential condition over R. Real closed
fields are model complete: see Marker, *Orsay Lectures*, §7, Theorem 7.14 and
Corollary 7.15, printed pp. 43–44
([author PDF](https://homepages.math.uic.edu/~marker/orsay/orsay3.pdf),
PDF pages 4–5). Thus either solvable condition would have a solution
(x₀,y₀)∈R². Its fifth inequality makes the resulting real member nonsingular,
and Sylvester's criterion makes it definite, contradicting §4.

The generic form is nondegenerate, so “not positive definite and not negative
definite” means indefinite over every chosen real closure. This proves the
all-orderings statement. No ordering of R(x,y) is identified with evaluation
at a real point. No inequalities involving infinitely many real coefficients
are transferred. If a different rational presentation is used instead of
A(x,y), its finitely many nonzero-denominator conditions must be included;
choosing the displayed affine linear matrix avoids them.

## What this review does not close

It does not prove the real symmetric-resolution theorem, the real cover
comparison, or the rank-three relative-anticanonical model from the original
geometric definition. It also does not audit the Albert/Pfister argument,
zero-cycle theorem, incidence dominance, or final birational comparison.
Subject to the listed inputs, Sections 3–4 supply the two actual hypotheses
needed later: a Clifford-index bound and indefiniteness at every ordering.
