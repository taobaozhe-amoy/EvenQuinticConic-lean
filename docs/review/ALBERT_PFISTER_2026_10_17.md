# Audit of the Albert–Pfister argument in Section 5

Date: 2026-10-17. Scope: Section 5 of
`docs/EVEN_THETA_CONNECTEDNESS_PROOF.md`.

## Verdict and exact scope

The argument is correct for the stated field and hypotheses. I checked the
specified book passages themselves and reconstructed the Clifford-algebra,
determinant, Pfister-subform, and final dimension arguments below. I found no
counterexample over `ℝ(x,y)` satisfying both hypotheses. There are explicit
counterexamples when either the ordering hypothesis or the restriction on the
base field is removed; see Section 8 below.

The precise conditional statement established by this audit is:

> Let `k = ℝ(x,y)`, and let `q` be a nonsingular five-dimensional quadratic
> form over `k`. If `ind C₀(q) ≤ 2` and `q` is indefinite over a real closure
> for every ordering of `k`, then `q` is isotropic over `k`.

More generally, the same proof works over a formally real field of
characteristic different from two for which
`I³(k) ∩ W(k)tors = 0`. The proof does **not** work over an arbitrary formally
real field: the three-variable counterexample below has exactly the two
quadratic-form hypotheses but is anisotropic.

This is a paper-level verification, not a Lean verification. It does not
independently establish that the form constructed from an even theta
characteristic satisfies the Clifford-index or every-ordering hypotheses.
Those are separate obligations in Sections 2–4. It also does not by itself
prove the later geometric steps or the original connectedness theorem.

## 1. Primary sources actually checked

The page numbers below are printed page numbers. The links specify the
corresponding one-based PDF page, avoiding the front-matter offset.

| Source | Exact location | Input needed here |
|---|---|---|
| Knus–Merkurjev–Rost–Tignol, *The Book of Involutions* (KMRT) | [Proposition 16.3 and the paragraph immediately following its statement, p. 235; PDF p. 253](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/involutions.pdf#page=253) | Six-dimensional forms of trivial discriminant are Albert forms; their even Clifford algebra identifies the associated biquaternion algebra. |
| KMRT | [Theorem 16.5, p. 236; PDF p. 254](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/involutions.pdf#page=254) | The pairs `(ind A, Witt index of its Albert form)` are `(4,0)`, `(2,1)`, `(1,3)`. |
| Elman–Karpenko–Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms* (EKM) | [Theorem 8.4 and Theorem 8.5, pp. 48–49; PDF pp. 56–57](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf#page=56) | Cancellation of a nonsingular summand; Witt decomposition. |
| EKM | [Section 11, Lemma 11.1, pp. 57–58; Proposition 11.6(2), p. 59; PDF pp. 65–67](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf#page=65) | Clifford relations, dimensions, and central simplicity of the odd-dimensional even Clifford algebra. |
| EKM | [Theorem 31.22, p. 128; PDF p. 136](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf#page=136) | The kernel of all signatures is the torsion subgroup of the Witt ring. |
| EKM | [Corollary 35.29, p. 159; PDF p. 167](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf#page=167) | For a finitely generated extension of transcendence degree `n` over a real closed field, `Iⁿ⁺¹` is torsion-free. |

The KMRT PDF is a university-hosted author text with unresolved internal
cross-reference placeholders in some passages. The numbered statements and
printed pages above are present and readable. Bibliographic identification:
[KMRT, DOI 10.1090/coll/044](https://doi.org/10.1090/coll/044),
[EKM, DOI 10.1090/coll/056](https://doi.org/10.1090/coll/056).

I also checked the [KMRT corrections page](https://www.math.uni-bielefeld.de/~rost/BoI-error.html),
its [page-sorted supplementary list](https://www.math.uni-bielefeld.de/~rost/boi/bois.txt),
and the [EKM author corrections dated 2026-09-06](https://sites.ualberta.ca/~karpenko/publ/corrections.pdf).
I found no correction to the passages used here. The supplementary KMRT list
itself distinguishes unverified remarks from author-checked corrections.

## 2. The two Clifford components: an actual isomorphism

Fix the convention `eᵢ² = aᵢ` for a diagonal quadratic form. Diagonalize

\[
q=\langle a_1,a_2,a_3,a_4,a_5\rangle,
\qquad d=a_1a_2a_3a_4a_5\in k^\times.
\]

Here `d` is an actual nonzero coefficient, not an element of a quotient group.
A different representative of its square class gives an isometric added line.
The signed discriminant in dimension five equals the determinant square class,
since `(-1)¹⁰ = 1`.

Set `r = q ⊥ ⟨−d⟩`. Then

\[
\det r=-d^2,
\qquad \operatorname{disc}r=(-1)^{15}(-d^2)=d^2,
\]

so the signed discriminant is trivial.

Use orthogonal Clifford generators `e₁,…,e₅,f`, with `f² = −d`. They
anticommute in distinct indices. Put

\[
z=e_1e_2e_3e_4e_5,\qquad w=zf.
\]

Direct multiplication gives

\[
z^2=(-1)^{10}d=d,
\qquad w^2=(-1)^{15}d(-d)=d^2.
\]

The product `w` anticommutes with each individual generator and therefore
commutes with every even product. Let `A = C₀(q)`, embedded in `C₀(r)` by
the first five generators. The Clifford monomial basis gives

\[
C_0(r)=A\oplus Aw.
\]

Indeed, even monomials in the first five generators span `A`. Multiplication
by `w` sends them, up to nonzero scalars, to the complementary even monomials
consisting of an odd number of those generators followed by `f`. Consequently

\[
C_0(r)\simeq A\otimes_k k[T]/(T^2-d^2)
\simeq A\times A,
\qquad a+bw\longmapsto(a+db,a-db).
\]

The inverse exists because `2d ≠ 0`. Equivalently the two central idempotents
are `(1 ± w/d)/2`, and projection onto either component identifies it with
`A`. The dimensions are `32 = 16 + 16`, as required.

Thus **both components are isomorphic to `C₀(q)` as algebras**, not merely
Brauer equivalent. There is no scalar change of `q` in this calculation and
no extra quaternion factor. This independently resolves the most
sign-sensitive assertion in the original paragraph.

## 3. Applying the Albert-form theorem

The nonsingular six-dimensional form `r` has trivial signed discriminant.
The classification at KMRT 16.3 therefore makes it an Albert form of the
biquaternion algebra identified by either even Clifford component. Section 2
identifies that algebra with `A = C₀(q)`.

KMRT 16.5 now applies to this actual algebra and actual form. The hypothesis
`ind A ≤ 2` excludes Witt index zero. Thus `r` is isotropic. If `ind A = 1`,
its Witt index is three, not one; this causes no difficulty because we need
only split off **one** hyperbolic plane:

\[
r\simeq\mathbb H\perp\rho,\qquad \dim\rho=4.
\]

All forms here are nonsingular. In particular the four-dimensional complement
is nonsingular. This use of the Albert classification does not assume that
the index bound itself implies isotropy of the original five-dimensional
form; that stronger assertion is false without further hypotheses.

## 4. The four-dimensional remainder and exact cancellation

The determinant of a hyperbolic plane is `−1` modulo squares. Since
`det r = −d²`, the determinant of `ρ` is a square. For dimension four this
is also its signed discriminant.

Here is the explicit Pfister calculation, so no classification of
four-dimensional forms is left implicit. Write

\[
\rho=\langle a,b,c,e\rangle,\qquad abce\in k^{\times2}.
\]

The ratio `e/(bc/a) = abce/(bc)²` is a square. Rescale the last basis vector,
and put `u = b/a`, `v = c/a`. This gives

\[
\rho\simeq a\langle1,u,v,uv\rangle
=a\bigl(\langle1,u\rangle\otimes\langle1,v\rangle\bigr)
=a\pi.
\]

This works whether or not `ρ` is anisotropic. Displaying the binary factors
also avoids any convention about signs in double-angle Pfister notation.

Add `⟨d⟩` to `q ⊥ ⟨−d⟩ ≃ H ⊥ aπ`. Since `⟨−d,d⟩ ≃ H`, we obtain

\[
q\perp\mathbb H\simeq
\bigl(a\pi\perp\langle d\rangle\bigr)\perp\mathbb H.
\]

Cancel the nonsingular hyperbolic planes by EKM 8.4, p. 48. The conclusion is
an actual isometry

\[
q\simeq a\pi\perp\langle d\rangle,
\]

not just equality of Witt classes. This precise cancellation reference should
be added to the original exposition.

## 5. The Pfister neighbor and its signatures

The form `π` represents `1` on its first coordinate. Hence `dπ` contains
the line `⟨d⟩`, and the preceding isometry embeds `q` as a genuine
five-dimensional subform of

\[
\Phi=a\pi\perp d\pi
=\langle a\rangle\otimes\pi\otimes\langle1,d/a\rangle.
\]

This is a scalar multiple of a three-fold Pfister form, of dimension eight.
It is unnecessary to assume that `a` is a square. Each of the three binary
factors has even dimension, so their Witt classes lie in the fundamental
ideal `I(k)`; multiplying their product by `⟨a⟩` preserves the ideal `I³(k)`.
Thus `[Φ] ∈ I³(k)`.

Fix any ordering and pass to its real closure. A binary factor `⟨1,t⟩` is
positive definite when `t > 0` and hyperbolic when `t < 0`. Therefore the
three-factor tensor product is positive definite or hyperbolic. For the
second case, tensoring a hyperbolic plane with a nonsingular form gives a
hyperbolic form: after diagonalizing the other factor, it is an orthogonal
sum of scalar multiples of hyperbolic planes. Multiplication by `a` can
reverse definiteness but preserves hyperbolicity.

The actual subform `q` is indefinite at this ordering. It cannot lie in a
positive or negative definite `Φ`. Therefore `Φ` is hyperbolic over this
real closure and has signature zero. The ordering was arbitrary.

Notice the logical direction: we use the existence of both signs on `q`
to exclude definiteness of its containing form. We do not infer global
isotropy of `q` directly from its signatures.

## 6. Why the torsion step is valid over ℝ(x,y)

Apply EKM 31.22 to the signatures just obtained. It gives

\[
[\Phi]\in W(k)_{\mathrm{tors}}\cap I^3(k).
\]

For `k = ℝ(x,y)`, the base field is real closed and the extension is finitely
generated of transcendence degree exactly two. These are precisely the field
hypotheses in EKM 35.29 with `n = 2`. Hence the displayed intersection is zero.

One must not replace this statement by `I³(k) = 0`. That stronger statement
is false: the class of

\[
8\langle1\rangle=\langle1,1\rangle^{\otimes3}
\]

lies in `I³(k)` and has signature eight at every ordering, so it is nonzero.
The assertion used in the original Section 5 is the correct torsion-free
assertion. Similarly, EKM 31.22 alone would give only torsion, not zero.

We conclude `[Φ] = 0` in the Witt ring. Since `Φ` is nonsingular, its Witt
decomposition has zero anisotropic part, so it is hyperbolic (EKM 8.5,
pp. 48–49). None of these steps invokes a vanishing theorem for the entire
Witt ring or silently passes from real points to all field orderings.

## 7. The final isotropic vector

Let `V` be the five-dimensional subspace carrying `q` in the eight-dimensional
space carrying `Φ`. A hyperbolic eight-dimensional form has a four-dimensional
totally isotropic subspace `U`. Elementary linear algebra gives

\[
\dim(U\cap V)\geq\dim U+\dim V-8=1.
\]

Any nonzero vector in the intersection is an isotropic vector of `q`, defined
over `k`. This proves the conditional statement at the beginning. No descent
from a real closure is being attempted at this last step: `Φ` was proved
hyperbolic over `k` itself.

## 8. Counterexamples to weaker readings

### 8.1 The index bound alone is insufficient, even over ℝ(x,y)

Take `q₊ = ⟨1,1,1,1,1⟩`. It is anisotropic over any ordered field. Nevertheless

\[
C_0(q_+)\simeq(-1,-1)\otimes(1,1)
\simeq M_2\bigl((-1,-1)\bigr)
\]

has index two. This formula follows directly inside the Clifford algebra:
`e₁e₂,e₁e₃` generate `(-1,-1)`, while `e₁e₂e₃e₄,e₁e₂e₃e₅` generate the
commuting quaternion algebra `(1,1)`. Their sixteen products are the even
Clifford monomials up to sign. The second quaternion algebra is split; the
first is division over an ordered field because its norm is a sum of four
squares. Thus no implication `ind C₀(q) ≤ 2 ⇒ q isotropic` is valid here
without the ordering condition.

### 8.2 Zero signatures alone do not imply a zero Witt class

Over `ℝ(x,y)`, the binary form `η = ⟨1,−(1+x²)⟩` has signature zero at every
ordering. It is anisotropic: `1+x²` is not a square in `ℝ(x,y)`, since its
valuation at the irreducible polynomial `1+x²` is one. Its Witt class is
therefore nonzero. EKM 31.22 makes that class torsion, consistently with the
proof above. What eliminates the torsion for `Φ` is its additional membership
in `I³`, together with EKM 35.29.

### 8.3 The field hypothesis is essential: a three-variable counterexample

Put

\[
k_3=\mathbb R(u,v,z),\qquad a=1+z^2,\qquad
q_3=\langle1,-a,-u,au,-v\rangle.
\]

This form is indefinite at every ordering: its first two coefficients have
opposite signs because `a > 0` in every ordered field extension of `ℝ`.
The same four Clifford monomials as in 8.1 give, with their actual squares,

\[
C_0(q_3)\simeq(a,u)\otimes(a^2u^2,-auv)
\simeq(a,u)\otimes M_2(k_3).
\]

For clarity, the first generator pair has squares `a,u`; the second has
squares `a²u²,−auv`. The pairs commute, each pair anticommutes internally,
and their sixteen products are independent even monomials. The second
quaternion algebra splits because its first entry is a nonzero square.
Consequently `ind C₀(q₃) ≤ 2`.

Despite both hypotheses, `q₃` is anisotropic. It is a subform of

\[
\Phi_3=\langle1,-a\rangle\otimes
        \langle1,-u\rangle\otimes\langle1,-v\rangle.
\]

Here is an elementary verification of anisotropy, without citing a further
isotropy theorem. The binary form `⟨1,−a⟩` is anisotropic over `E = ℝ(z)`:
the irreducible polynomial `1+z²` has odd valuation and so cannot be a square
in `E`.

If a diagonal form `ψ` is anisotropic over a field `E`, every nonzero value of
`ψ` on a vector over `E((t))` has even `t`-valuation. Indeed, factor out the
smallest power of `t` occurring among its coordinates. The leading coefficient
of the remaining value is the value of `ψ` on a nonzero residue vector; it
cannot vanish by anisotropy. Thus the valuation is twice the minimum coordinate
valuation. It follows that `ψ ⊥ (−t)ψ` is anisotropic over `E((t))`: nonzero
values of its two blocks have opposite valuation parity and cannot cancel.

Apply this argument first with `t = u`, then with `t = v`. It proves that
`Φ₃` is anisotropic over `ℝ(z)((u))((v))`. The rational function field `k₃`
embeds there, so `Φ₃`, and hence `q₃`, is already anisotropic over `k₃`.

This also exhibits a nonzero torsion class in `I³(k₃)`: `Φ₃` has zero
signature at every ordering because the binary factor `⟨1,−a⟩` does.
There is no contradiction with EKM 35.29, which in transcendence degree
three guarantees torsion-freeness of `I⁴`, not `I³`.

## 9. Recommended clarification of the original Section 5

No change to its mathematical conclusion is needed. Its compressed steps
should be expanded or linked to this verification as follows:

1. Choose an actual determinant representative `d ∈ k×` before using it as
   a coefficient.
2. Include the volume-element calculation proving
   `C₀(q ⊥ ⟨−d⟩) ≃ C₀(q) × C₀(q)`.
3. Cite KMRT 16.3 and 16.5 with printed pages 235–236; do not claim that the
   six-dimensional form always has Witt index exactly one.
4. Include the diagonal calculation for the four-dimensional remainder and
   cite EKM 8.4, p. 48, for cancellation.
5. Retain explicitly both the every-ordering hypothesis and the
   transcendence-degree-two specialization. Neither can be silently dropped.
6. State the torsion intersection, rather than any vanishing of `I³` itself,
   and keep the distinction between this paper proof and a Lean proof.

Only this review file was added in this audit; the proof document and Lean
sources were not modified.
