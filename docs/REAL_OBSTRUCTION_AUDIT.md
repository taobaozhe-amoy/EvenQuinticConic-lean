# Audit of the real and quadratic-form part of the proposed argument

Date: 2026-10-04. This is a mathematical audit, not a Lean certificate.

A self-contained proof revisited on 2026-10-15, including the elementary
theta-ineffectivity argument and a direct real-connectedness proof without
resolution, is recorded in [EVEN_THETA_CONNECTEDNESS_PROOF.md](EVEN_THETA_CONNECTEDNESS_PROOF.md).
The source modules do not yet implement the geometric objects or the major
theorems invoked here. In particular, passing the current Lean audit does not
certify the conclusion discussed below.

**Status.** Sections 1–6 give a paper-level proof under the standard
geometric meaning of a smooth projective geometrically standard conic
bundle. They invoke classical theorems explicitly listed in section 7.
No fatal implication error was found in this audit. The theorem is not
Lean-checked: in particular, the project has no Lean construction of the
relative anticanonical model, Brauer residues, the Albert/Pfister argument,
the zero-cycle theorem, or the birational correspondence of schemes.
Consequently the repository must continue to report the full formalization
as unfinished. Section 8 explains why the inspected example does not
contradict this paper argument.

This is a candidate argument and a record of an informal review, not a
certification of its complete correctness. In particular, the statement
that this review found no fatal error does not rule out an error or a
missing hypothesis in its unformalized deductions. Successful compilation
of the separate Lean lemmas does not strengthen that claim. See
[the current proof boundary](PROOF_STATUS.md).

The arithmetic implication that was previously least precise is valid:

> A nondegenerate five-dimensional form over `R(x,y)` whose even Clifford
> algebra has index at most two, and which is indefinite at every ordering,
> is isotropic.

The proof is supplied in section 5, with precise references. The real twist
and constant Brauer class must first be identified; simply constructing a
complex symmetric matrix is insufficient. Sections 1–4 give the proposed
geometric identification explicitly. They are original deductions using
the stated standard geometric inputs, not quotations of a theorem claiming
real rationality of every even-quintic conic bundle.

## 1. Geometric inputs and conventions

Let `S=P²_R`, `F=R(S)`, and let `X→S` be a smooth projective conic bundle in
the usual flat, relative-anticanonical sense. Let its discriminant `C` be a
smooth plane quintic. The relative anticanonical embedding presents it as
the zero locus of an `L`-valued quadratic form on a rank-three vector bundle
`E`. The discriminant section belongs to `(det E)^(-2)⊗L³`.

Smoothness of `C` means that the form has rank exactly two along `C`: rank
at most one would make all first derivatives of the determinant zero.
Its discriminant double cover parametrizes the two geometric line
components. Write `η` for its trace-zero line bundle, so `η²≅O_C`, and
`θ=η⊗O_C(1)`. Here an actual cover over `R`, including its multiplication,
is required, not only the complex isomorphism class of `η`.

Here “geometrically standard” may instead be defined by proper flatness,
a smooth generic conic, smooth projective total space, and geometric
relative Picard number one. These conditions supply the same model.
Over `C`, the numerical class of `-K_X` is a positive multiple of a
relative ample class, since the relative numerical divisor space has
dimension one and its degree on the generic conic is positive. Relative
ampleness follows; the relative anticanonical conic-bundle theorem gives
the rank-three pushforward and its closed immersion. These constructions
descend to `R`: formation of the pushforward commutes with the field
extension, and local freeness and closed immersion descend faithfully
flatly. Flatness and the geometrically integral generic fiber rule out
additional components of the smooth total space. Thus no unexplained
geometric-integrality assumption is being supplied by the notation.

Assume geometric evenness. The separate theta lemma gives `h⁰(θ_C)=0`.
Beauville's real symmetric resolution produces a symmetric linear matrix
`M(t)=t₀M₀+t₁M₁+t₂M₂` with determinant defining `C` and resolution

```
0 → O(-2)^5 → O(-1)^5 → i_*θ → 0.
```

This uses the real line bundle, not the descent of an arbitrary complex
matrix. Let `q` be its generic five-dimensional form.

For an even-rank nondegenerate form the signed discriminant is
`(-1)^(n(n-1)/2)det`. Thus the residual rank-two form uses `-det`, whereas
the residual rank-four form uses `+det`. These signs cannot be interchanged.

## 2. The real cover is determined on the pseudoline

The real locus of a smooth odd-degree plane curve has a pseudoline `J`.
The restriction of `O(1)(R)` to `J` is nonorientable. Evaluating first
Stiefel–Whitney classes on `J` in

```
O(C) ≅ (det E)^(-2)⊗L³
```

shows that `L(R)|_J` is also nonorientable. Transporting a trivialization
of `L` once around `J` reverses its sign. Congruence changes of the vector
bundle frame preserve inertia, so the rank-two quotient form on `J`
has the same positive and negative indices. Its signature is `(1,1)`.
Consequently the original cover has real fibers above every point of `J`.

The matrix form is `O(1)`-valued on `O^5`. Its rank-four quotient along
`J` similarly has signature `(2,2)`, so its signed-discriminant cover also
has real fibers there.

To compare their underlying line bundles, put `K=rad(M|_C)` and `W=O_C^5/K`.
Twisting the resolution by two identifies the cokernel of
`O_C^5→O_C(1)^5` with `θ(2)`. Symmetry identifies that cokernel with
`K^*⊗O_C(1)`, hence

```
K ≅ θ^(-1)(-1),
det W ≅ θ(1),
det W ⊗ O_C(-2) ≅ θ(-1)=η.
```

The last line is the trace-zero line of the rank-four signed-discriminant
cover. Two square trivializations of this same line differ by a nonzero
global real constant, since `C` is geometrically integral and projective.
Up to squares there are only two possibilities. Evaluation at any point
of `J`, where both covers split, selects the same possibility. This fixes
the real twist without an unsupported choice of square root.

Scaling `M` by a real scalar would not fix an incorrect twist: the
rank-four determinant changes by the fourth power of that scalar.

## 3. Comparison of the actual Brauer classes

Let `α∈Br(F)[2]` be the class of the original generic conic, and let
`β=[C₀(q)]`. Both are unramified away from `C`. Their residues along `C`
are the respective signed-discriminant covers, now identified over `R`.

The residue signs can also be checked directly. For a diagonal rank-five
form one has the Brauer-class formula

```
C₀(<a,b,c,d,e>) = (-ab,-ac) + (abcd,abce).
```

At a simple degeneration `e=πu`, with the other coefficients units, its
residue is `abcd`, the discriminant of the residual rank-four form.
For a rank-three form `<a,b,πu>` the formula `(-ab,-aπu)` gives residue
`-ab`, as required for the rank-two conic degeneration. Local bundle
trivializations show that there is no extra divisor of ramification at
the boundary of a chosen affine chart.

Brauer purity and `Br(P²_R)=Br(R)` give `β-α∈Br(R)`. At a nearby real
point outside `C` and near `J`, the original conic is isotropic and the
matrix has signature `(3,2)` or `(2,3)`. Both Brauer classes specialize to
zero. Evaluation therefore forces the constant difference to be zero:

```
β=α,       ind C₀(q)≤2.
```

This step needs equality of the covers as real covers. Equality after
complexification would not establish it.

## 4. No definite real member, and all orderings

For real rank-five forms the even Clifford class is split in signatures
`(3,2)` and `(2,3)`, and quaternionic in signatures `(5,0)`, `(4,1)` and
their negatives. These values follow directly from the preceding two-symbol
formula and the real quaternion rule: `(a,b)` is nonsplit precisely when
both entries are negative.

Suppose a definite member existed. Join it by a path to a member near `J`
of signature `(3,2)` or `(2,3)`. A boundary point of the definite locus is
on `C`, and smoothness of `C` makes the residual form rank four and
definite. Its signed discriminant is positive, so its cover splits there.
The identified original conic therefore degenerates into two real lines.
It has real smooth points near that fiber; equivalently its local
rank-three equation has a rank-two indefinite block, so `α` is split
on both neighboring sides. But `β` is quaternionic at neighboring
definite members. This contradicts `α=β`.

Thus every nonsingular real member is indefinite. To pass to an arbitrary
ordering of `F`, embed `F` in its real closure. If the generic matrix were
definite there, Sylvester's principal-minor inequalities would give a
finite system of strict polynomial inequalities in the parameters, with
real coefficients, solvable in a real closed extension of `R`. Real-closed
field transfer gives a real solution. Its determinant is nonzero, and it
would be a definite real member, a contradiction. Hence the generic form
is indefinite at every ordering. This transfer concerns a finite
semialgebraic condition; it is not an assertion that every ordering is
evaluation at a real point.

## 5. The five-dimensional arithmetic lemma

Let `k` have characteristic different from two, let `q` be a nondegenerate
five-dimensional form, and set `d=det(q)` in `k*/k*²`. Suppose
`ind C₀(q)≤2`. The six-dimensional form `r=q⊥<-d>` has trivial signed
discriminant and `C₀(r)≅C₀(q)×C₀(q)`. It is an Albert form for the
degree-four algebra `C₀(q)`. The Albert index criterion therefore makes
`r` isotropic. Write `r≅H⊥ρ`, where `ρ` has dimension four and trivial
signed discriminant. Such a form is `aπ`, with `π` a two-fold Pfister
form. Witt cancellation gives

```
q ≅ aπ ⊥ <d>.
```

It follows that `q` embeds in the scaled three-fold Pfister form
`aπ⊗<1,d/a>`. This also covers the split case; there is no assumption
that the ambient field is linked.

Now take `k=R(x,y)` and assume `q` indefinite at every ordering. A
three-fold Pfister form has signature zero or is definite at each
ordering. Since it contains the indefinite five-dimensional form, the
ambient eight-dimensional form has signature zero everywhere. Pfister's
local-global theorem makes its Witt class torsion. The torsion-freeness
of `I³(R(x,y))` makes this class zero, so the ambient form is hyperbolic.
A five-dimensional subspace of a split eight-dimensional quadratic
space meets a four-dimensional totally isotropic subspace nontrivially.
Thus `q` is isotropic.

## 6. From generic isotropy to a rational incidence model

Write `Q_i(z)=zᵀM_i z` in five variables, and let
`Γ=V(Q₀,Q₁,Q₂)⊂P⁴_R`. Colliot-Thélène–Levine's zero-cycle theorem applies
to these three degree-two forms in five variables. A rational point on
the generic quadric gives a zero-cycle of degree one on `Γ`. Closed-point
degrees over `R` are one or two, so such a cycle forces `Γ(R)≠∅`.

Choose `P∈Γ(R)` and coordinates `P=[1:0:0:0:0]`. Then

```
Q_i(x₀,y)=2x₀ l_i(y)+r_i(y),       y∈R⁴,
```

with `l_i` linear and `r_i` quadratic. The three `l_i` are independent.
Otherwise some nonzero parameter `t` would give `M(t)P=0`. If its rank
is at most three, the determinant curve is singular there. If its rank is
four, its adjugate is a multiple of `PPᵀ`, and all determinant derivatives
are multiples of `Q_i(P)=0`, again a contradiction.

Hyperbolic reduction at `P` gives the generic conic of the incidence
variety

```
Z={(t,y)∈P²×P³ : Σt_i l_i(y)=0, Σt_i r_i(y)=0}.
```

The two coefficient rows have an independent minor on a nonempty open
subset of `P³`. Indeed, if all their minors vanished identically, choosing
coordinates with `l_i=y_i` and using unique factorization gives
`r_i=h l_i` with a common linear `h`. Every `Q_t` would then factor as
`l_t(2x₀+h)`, contradicting the nonzero determinant.

On the minor open, the cross product of these rows supplies the unique
point `t`, so the graph is birational to `P³`. This component dominates
`P²`: each fiber of `Z→P²` has dimension one. A fiber equal to a whole
plane would have `r_t` divisible by `l_t`, forcing `Q_t` to have rank at
most two and again making the determinant curve singular. Thus the
component of `Z` dominating `P²` is rational.

Its generic conic is defined by the three-dimensional remainder after splitting off a
hyperbolic plane from `q`, and consequently has even Clifford class `β`.
Since `β=α`, the original generic conic is isomorphic to it. Therefore
this construction, once the preceding geometric inputs are supplied,
gives a real birational map from `X` to `P³`.

For a smooth projective real rational variety the real locus is connected.
One may resolve a birational map from `P³` by blowups along smooth real
centers. Such blowups have nonempty connected real fibers and preserve
connectedness. The resulting proper morphism onto `X` has image containing
a dense open subset of `X(R)`; smoothness makes that subset Euclidean
dense in every component, and properness makes the image closed. The
image is therefore all of `X(R)` and is connected.

## 7. Exact sources checked

* A. Beauville, *Determinantal hypersurfaces*, Proposition 4.2(a), together
  with the ground-field convention in §0.3 and the symmetric-resolution
  results of §2. [Author preprint](https://arxiv.org/pdf/math/9910030).
* B. Poonen, *Rational Points on Varieties*, Theorem 6.8.3 (Brauer purity)
  and Proposition 6.9.9 (`Br(k)≅Br(Pⁿ_k)`), printed pp.197, 200.
  [Author PDF](https://math.mit.edu/~poonen/papers/Qpoints.pdf).
* Y. Prokhorov, *The rationality problem for conic bundles*, Definition 3.1
  and Theorem 3.2: the relative anticanonical model over the complex
  numbers, used above together with faithful flat descent. Its Proposition
  8.1 is a complex rationality theorem and is **not** being applied over
  the real numbers. [Author preprint](https://arxiv.org/pdf/1712.05564).
* M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol,
  *The Book of Involutions*, Proposition 16.3 and Theorem 16.5, printed
  pp.235–236: the six-dimensional discriminant-one form and its Albert
  algebra, and the exact index/Witt-index criterion.
  [University-hosted preprint](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/involutions.pdf).
* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory
  of Quadratic Forms*, Theorem 31.22 (local-global theorem) and Corollary
  35.29 (torsion-freeness of `I^(n+1)` over transcendence-degree `n`
  extensions of a real closed field), printed pp.128, 159.
  [Author PDF](https://www.math.ucla.edu/~merkurev/Book/Kniga-final/Kniga.pdf).
* J.-L. Colliot-Thélène and M. Levine, *Une version du théorème d'Amer et
  Brumer pour les zéro-cycles*, Theorem 3, pp.5–6 of the 4 December 2009
  author version. This is the zero-cycle theorem for an arbitrary system,
  not the two-quadric rational-point theorem.
  [Author PDF](https://www.imo.universite-paris-saclay.fr/~jean-louis.colliot-thelene/CTLevine4dec2009.pdf).

The elementary real-topological, residue-symbol, incidence, and Pfister-
embedding deductions in this note are stated as deductions, not attributed
verbatim to these sources. Their implementation in Lean remains absent.
The quoted classical inputs alone do not turn the current collection of
algebraic Lean lemmas into a formal proof of the original theorem.

## 8. Independent check of the supplied construction's parity

The inspected local snapshot of `RealConicBundles-Problem3-lean/README.md`,
at commit `8b2e7df967727bf82d1c3430128b928e338c31b9`, explicitly says that
its statement imposes no even-theta assumption. Its matrix is

```
M = [[2A,0,v²], [0,2B,w²], [v²,w²,2C]],
deg A=deg B=1,    deg C=3.
```

This is a different graded symmetric presentation from the `5×5` linear
presentation. Its cokernel resolution is

```
0 → O(-2)^2 ⊕ O(-3) --M--> O(-1)^2 ⊕ O → i_*θ → 0.
```

For a nonzero smooth discriminant, the cokernel is a line bundle on the
discriminant. To identify it with the theta characteristic of the actual
cover, regard the same form as `O(1)`-valued on `E=O²⊕O(-1)`.
The cokernel of `E→E*⊗O(1)` is `θ(2)`, so the radical is
`K=θ^(-1)(-1)`. The rank-two quotient has

```
det(E/K)=det(E)⊗K^(-1)=θ,
η=det(E/K)⊗O(-1)=θ(-1).
```

Thus this is the theta line bundle associated with the discriminant
double cover, irrespective of its real square-trivialization twist.
Since `H¹(P²,O(m))=0` for every integer `m`, the displayed resolution
gives

```
h⁰(C_C,θ_C)=h⁰(P²_C,O(-1)^2⊕O)=1.
```

Under the smooth-discriminant properties claimed and proved for that
matrix, the associated theta characteristic is therefore **odd**, not
even. This is a paper-level calculation of that parity; the inspected
README does not claim a Lean theorem about theta parity. It agrees with
the construction as projection of a cubic threefold from a line. The
assertion that this example has two real components is compatible with
the even-theta obstruction audited above.
