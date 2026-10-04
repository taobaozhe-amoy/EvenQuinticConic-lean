# The theta-characteristic bridge: mathematical proof and exact interfaces

This note supplies a mathematical proof of the first geometric lemma in the
proposed argument. It is not a claim that the complete geometric theorem has
been checked by Lean. The section-theoretic implication is formalized for
actual schemes and module sheaves. The constructed plane curve now supplies
both actual quadratic-section surjectivity and quartic injectivity. The
normal theta-framed refinement and perfect theta square pairing remain
explicit geometric inputs, and have not yet been constructed from the
original smooth-quintic and double-cover hypotheses. Sections 4–5 state the
checked implication and the remaining instantiation work.

## 1. Precise lemma

Let `k` be an algebraically closed field of characteristic different from two,
let `C = V(F)` be a smooth plane quintic over `k`, and put `H = O_C(1)`.
Let `theta` be a line bundle with a specified isomorphism
`psi : theta^⊗2 ≅ H^⊗2`; by adjunction these are precisely the theta
characteristics. Then

> If `dim_k H^0(C, theta) >= 2`, then `theta ≅ H` and
> `dim_k H^0(C, theta) = 3`.

In particular every even theta characteristic on a smooth plane quintic has
no nonzero global section. This statement is about theta characteristics on
the discriminant curve; it is not a rationality or real-connectivity theorem
for a conic bundle.

### Proof

The smooth plane curve is integral. Choose independent sections
`s,t ∈ H^0(C,theta)`. The exact sequence

```
0 → O_P²(-3) --F--> O_P²(2) → O_C(2) → 0
```

and `H^0(P²,O(-3)) = H^1(P²,O(-3)) = 0` show that restriction identifies
homogeneous quadratic polynomials with `H^0(C,H^⊗2)`. Consequently there are
unique homogeneous conics `A,B,D` with

```
A|_C = psi(s⊗s),   B|_C = psi(s⊗t),   D|_C = psi(t⊗t).
```

The product identity holds as an identity of sections of `H^⊗4`, since the
same isomorphism `psi` was used in all three products. Thus
`(AD-B²)|_C = 0`. The degree-four restriction map is injective: the kernel is
`H^0(P²,O(-1)) = 0`. Therefore `AD = B²` as polynomials. Equivalently, one
can use `AD-B² ∈ (F)` and the strict degree inequality `4 < 5`.

The polynomials `A,D` are nonzero. They cannot satisfy `A = c D` for any
`c ∈ k`: such an equality implies `s² = c t²` at the generic point.
Choose `lambda ∈ k` with `lambda² = c`. Factoring gives
`(s-lambda*t)(s+lambda*t)=0`. The generic fiber is a one-dimensional vector
space over the function field, so one factor vanishes. A global section of a
line bundle on an integral curve is determined by its generic value; hence
`s = lambda*t` or `s = -lambda*t`, contradicting independence.

The polynomial classification proved in `HomogeneousConics.lean` now gives

```
A = c a²,   B = c a b,   D = c b²,
```

where `c ∈ k*` and `a,b` are homogeneous linear polynomials. The section
`a|_C` is nonzero, since its square is `c⁻¹ psi(s²)` and `s` is nonzero.
Let `E = div_theta(s)` and `Z = div_H(a|_C)` be the zero divisors of these
nonzero sections. Taking divisors in the exact section identity
`psi(s²)=c(a|_C)²` gives

```
2 E = 2 Z.
```

This is equality in the free abelian group of divisors on the smooth curve,
so it implies `E=Z`. The section-divisor identifications yield
`theta ≅ O_C(E) = O_C(Z) ≅ H`.

Finally restriction in degree one is an isomorphism, using
`H^0(P²,O(-4)) = H^1(P²,O(-4)) = 0`; consequently
`h^0(C,H) = dim_k k[X0,X1,X2]_1 = 3`.
If `h^0(C,theta)` is even and nonzero, it is at least two, and the preceding
argument makes it equal to three, a contradiction. Therefore it is zero.

### Where cancellation is legitimate

It would be incorrect to cancel two in the Picard group merely from
`theta² ≅ H²`: its two-torsion is exactly what is under investigation.
The proof cancels two only after obtaining equality of actual zero divisors
from the particular section identity `psi(s²)=c a²`.

There is also a local proof of the same last step. The rational section
`r=s/a` of `eta=theta⊗H⁻¹` satisfies `r²=c` under the induced isomorphism
`eta²≅O_C`. At every closed point, choose a regular frame for `eta`. If
`r=q e`, the square-trivialization sends `e²` to a local unit `g`, so
`q² g=c`. The discrete valuation of `q` is zero. Thus `r` extends to a
nowhere-vanishing regular section, trivializing `eta`. This does not require
choosing a square root of `c`.

The projective-space cohomology calculations used here are recorded in
[Stacks Project, Tag 01XS](https://stacks.math.columbia.edu/tag/01XS).
The identification of a line bundle with the divisor of a regular section is
[Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0).
On a smooth curve the local rings at closed points are discrete valuation
rings, so equality of the associated Weil divisors is equality of the
Cartier divisors as used above.

## 2. Weighted generic restriction model, with no square-root extension

Here is a precise model compatible with the polynomial calculations. Put
`L=k(C)`. Choose nonzero rational sections `e` of `H` and `tau` of `theta`.
Write

```
Xi|_C = fi e,       s = alpha tau,       t = beta tau,
psi(tau²) = u e²,
```

where `fi,alpha,beta ∈ L` and `u ∈ L*`. Let `T` be an indeterminate and
set `R=L[T]`. Define the `k`-algebra map

```
phi : k[X0,X1,X2] → L[T],   Xi ↦ fi T.
```

If `S=alpha T` and `V=beta T`, the lifts satisfy the weighted identities

```
phi(A)=u S²,   phi(B)=u S V,   phi(D)=u V².
```

The coefficient `u` is a constant polynomial in `L[T]`; it is nonzero.
These identities are enough for the algebraic argument. One need not adjoin
`sqrt(u)`, and one must not simply assume that this square root already
belongs to `L`: that would prematurely trivialize the two-torsion class.

The map sending a global theta section `s` to its generic coefficient
`alpha` is `k`-linear and injective. Multiplication by `T` is injective in
`L[T]`. Therefore independence of the geometric sections implies
`LinearIndependent k ![S,V]`. It does not imply independence over `L`.

The common multiplier `u` cancels in the two required arguments:

* `phi(AD-B²)=u²(S²V²-(SV)²)=0`.
* If `A=cD`, then `u S²=c u V²`, hence `S²=c V²`, contradicting the
  independent-squares theorem over the algebraically closed field `k`.

The nonzero square lifts follow similarly from `u ≠ 0` and `S,V ≠ 0`.
The already proved polynomial classification then applies.

### Exact kernel statement

The kernel of this graded map is `(F)`. Indeed, write a polynomial as a sum
of homogeneous pieces `P=Σ P_n`. Its image is `Σ P_n(f0,f1,f2) T^n`.
Uniqueness of polynomial coefficients shows that `phi(P)=0` exactly when
all the generic sections `P_n|_C` vanish. Generic vanishing is equivalent
to vanishing of the global section. Since the ideal sheaf of the plane
hypersurface is `O_P²(-5)` with inclusion given by multiplication by `F`,
the homogeneous kernel in degree `n` is `F · k[X0,X1,X2]_(n-5)` (zero if
`n<5`). Summing the pieces gives `P∈(F)`.

The indeterminate is essential if one wants this full ring-kernel identity.
Replacing `phi` by `Xi↦fi ∈ L` collapses degrees: a domain embedding
`k[X0,X1,X2]/(F) ↪ L` would contradict their transcendence degrees two
and one. The direct proof in §1 needs only degree-two surjectivity and
degree-four injectivity and therefore avoids formalizing this full kernel
statement altogether.

### Recovering the square class, if that interface is useful

For a nonzero section `s=alpha tau` and `a|_C=v e`, the factorization
`A=c a²` gives `u alpha²=c v²`. Here `alpha,v≠0`. If `d²=c` in `k`, then

```
u = (d v / alpha)².
```

This is a conclusion of the factorization, not an input to it. In terms of
rational divisors, `div(u)=2(div(tau)-div(e))`, and the same divisor
cancellation as above reconstructs `theta≅H`. The direct rational-section
argument with `s/a` is shorter and avoids choosing `d`.

## 3. What the real determinantal step actually requires

Let the original discriminant curve and its étale double cover be defined
over `R`. In characteristic different from two, the trace decomposition of
an étale double cover gives an actual real line bundle `eta` and an
isomorphism `eta²≅O_C`. Hence `theta=eta⊗O_C(1)` is an actual real line
bundle, not merely an invariant complex isomorphism class. If its geometric
parity is even, §1 applied after base change to `C` gives
`H^0(C_C,theta_C)=0`, hence also `H^0(C,theta)=0` by field base change.

Beauville's *Determinantal hypersurfaces*, Proposition 4.2(a), provides the
symmetric linear resolution of an ineffective theta characteristic, with
determinant the defining plane equation. The paper's §0.3 explicitly works
over an arbitrary field, and its symmetric-resolution theorem assumes
characteristic different from two. Therefore the existence theorem applies
directly over `R` to this actual real line bundle; an additional informal
claim that an arbitrarily chosen complex matrix descends is unnecessary.
See [the original paper, §§0.3, 2 and 4.1](https://arxiv.org/pdf/math/9910030).

This observation does not identify the signed real discriminant double
cover of the resulting five-dimensional form with the original cover.
That comparison must retain the chosen square-trivialization and its real
square class. The cofactor sign issue, Brauer-class comparison, isotropy,
real rationality and connectedness remain distinct obligations.

## 4. Checked conditional theorem on actual sheaves

`ThetaIneffectivity.lean` now proves the section-theoretic implication using
actual `Scheme.Modules` objects, actual global sections, actual natural
bilinear pairings, and scalar structures induced by the actual scheme
structure morphism. The objects are not predicates named after the desired
conclusion.

### Precise inputs

Let `K` be algebraically closed and `X` an actual integral scheme over
`Spec K`. Supply actual module sheaves `Θ,H,T`, natural square pairings
`μ:Θ×Θ→T` and `ν:H×H→T`, and a cover by nonempty affine opens with
integrally closed coordinate rings and coherent rank-one frames for all
three sheaves. The actual local maps `TensorProduct.lift (μ.app U_i)` and
`TensorProduct.lift (ν.app U_i)` must be bijective.

Choose three actual global sections `e₀,e₁,e₂` of `H`. The two restriction
inputs are:

- `h2`: surjectivity of the actual map `quadraticSectionMap ν e` from the
  homogeneous degree-two polynomial submodule to `Γ(X,T)`. This map is
  explicitly constructed from the six quadratic monomials using `ν`.
- `h4`: injectivity of homogeneous quartic evaluation at the three actual
  generic coefficients of these sections in a chosen nonempty framed open.

Under these inputs, `theta_iso_hyperplane_of_independent_sections` proves
that two independent actual `Θ` sections force an actual `Θ ≅ H`.
`theta_iso_hyperplane_of_finrank_ge_two` obtains the same result from a
dimension lower bound of two.

The final theorem `even_theta_ineffective_of_restriction_maps` adds only
even `finrank K Γ(X,Θ)` to those inputs and proves `s=0` for every actual
global section `s`. It internally derives both `h⁰(H)=3` and
finite-dimensionality of `Γ(X,Θ)`.

Specifically, `ThetaFiniteDimension` constructs a surjective map from `K⁶`
to the actual square section space using the six quadratic monomials. If a
nonzero theta section exists, pairing with it is an actual injective linear
map into that finite-dimensional space; otherwise the theta section space
is already zero. `HyperplaneDimension` proves that the three coordinate
sections are independent using `h4` and span using `h2`, then constructs
their actual basis to obtain dimension three. Thus no finite-dimensionality
or dimension-three hypothesis remains in the strongest theorem. This also
avoids requiring a separate degree-one cohomology proof solely to obtain
`h⁰(H)=3`. An unrestricted Lean `finrank = 0` is never used by itself to
conclude that a vector space is zero.

### How the inputs lead to the conclusion

| Stage | Checked construction or inference |
| --- | --- |
| Base-field action | `SchemeScalarAction` pulls constants back along `X→Spec K`, constructs scalar towers, and makes the actual generic coefficient map `K`-linear and injective |
| Three quadratic lifts | `QuadraticSections` constructs actual sections from quadratic polynomials; `h2` supplies lifts of `μ(s,s)`, `μ(s,t)`, and `μ(t,t)` |
| One common multiplier | `RankOnePairing` and `ModulePairing` derive the generic formula `gen(μ(s,t))=u gen(s)gen(t)` from the same actual pairing; local tensor-perfectness makes its computed coefficient a unit |
| Polynomial factorization | Quartic injectivity gives `AD=B²`; the verified homogeneous classification yields `A=ca²`, `B=cab`, `D=cb²` |
| A genuine section identity | `ThetaSectionBridge` evaluates the linear polynomial in the three actual `H` sections, proves this section is nonzero, and uses generic injectivity to obtain an actual global square-pairing identity |
| Local comparison | `PairingComparison` derives local unit weights from that identity; `GenericPointInjection` and `LocalSquareUnit` extend the resulting quotient to a unit in each actual affine coordinate ring |
| Actual sheaf isomorphism | `FrameComparison` constructs local linear comparison maps and proves their overlap equality; `ModuleHomGluing` glues an actual isomorphism sending the constructed `H` section to the original `Θ` section |
| Finite-dimensionality | `ThetaFiniteDimension` derives finite-dimensional square sections from six quadratic generators and finite-dimensional theta sections from an actual pairing injection |
| Hyperplane dimension | `HyperplaneDimension` proves that the actual three coordinate sections are a basis using `h2` and `h4`, hence `h⁰(H)=3` |
| Dimension and parity | `GlobalSectionDimension` obtains a base-field-linear equivalence of actual global section spaces; `ThetaIneffectivity` uses the derived dimensions to rule out positive even dimension |

The stronger comparison theorem no longer takes the ratio-transition
identities or compatible local maps as independent inputs: those are proved
from the genuine global sections and coherent frames. It constructs
`Θ ≅ H` directly. Thus the formal route does not need to define
`Θ⊗H⁻¹` and then cancel a tensor factor, or to formalize the divisor
argument in §1.

The pinned mathlib has a tensor construction for presheaves of modules.
It would be incorrect to assume that the tensor product of global sections
always computes global sections of a tensor-product sheaf. The present API
uses actual natural bilinear pairings and requires tensor-map bijectivity
only on the specified framed local opens.

### Assumption audit

Nonempty opens of an integral scheme contain its generic point, so every
pairwise intersection of the covering opens is also nonempty. This justifies
the generic equality tests. Empty subopens are handled by the actual sheaf
restriction and gluing statements and are not mapped injectively into a
field. Every covering theorem retains the actual union condition.

Integrality and integral closedness are separate hypotheses: the first
supplies generic injection, while the latter is used for extending roots of
units on affine opens. The square-quotient result requires a nonzero generic
denominator, not a denominator that is locally a unit. Common zeros of
regular numerators and denominators are therefore allowed.

## 5. Actual geometric realization and remaining inputs

The project now constructs `PlaneCurveScheme F` as the reduced induced
closed subscheme of `V(F)` inside the actual projective plane. It constructs
the closed immersion, the structure morphism over the base field, and three
affine coordinate charts covering the curve. The explicit polynomial
hypotheses—homogeneity, degree greater than one, and primality of `(F)`—give
integrality, the actual generic point's image, and nonemptiness of the
charts. These conclusions are proved, not added as scheme properties.

`ProjectiveCoordinateSections` constructs the actual regular functions
`Xⱼ/Xᵢ` and their unit cocycle on chart intersections. `PullbackTransition`
pulls the cocycle back along the actual curve inclusion. The `LineBundle*`
construction modules then construct a genuine module sheaf from that data:
its sections are compatible families of regular functions, its sheaf axiom
comes from the actual structure sheaf, and its local frames have the
explicit inverses `r ↦ (gⱼᵢ r)ⱼ`. `PlaneHyperplaneSheaf` supplies three actual
global coordinate sections and proves that their generic coefficients are
the actual normalized projective coordinates. The target hyperplane sheaf
is no longer merely assumed to exist. `LineBundlePairing` multiplies the
cocycle with itself to construct the actual square sheaf and its natural
multiplication pairing. Explicit tensor linear equivalences in the
constructed frames prove local tensor-perfectness, with coefficient one,
on every chart subopen. This is a local assertion; it does not identify a
tensor product of global sections with all square-sheaf sections.

`ProjectiveQuarticRestriction` proves homogeneous low-degree injectivity
directly in the actual curve function field. It uses genuine projective
chart fractions, their pullbacks, and the homogeneous prime at the actual
generic point. `ProjectiveBaseScalars` identifies chart constants with the
canonical algebra map induced by the structure morphism. Thus the former
comparison between algebraic chart coordinates and actual generic
coefficients has been established. In particular,
`planeQuintic_hyperplane_quartic_injective` gives the exact canonical-`aeval`
quartic statement for the three constructed global hyperplane sections.

`PlaneHomogeneousKernel` strengthens the restriction result: in every
homogeneous degree, generic vanishing is exactly membership in `(F)`.
Retaining degree in a variable `T` computes the complete graded kernel and
constructs an actual embedding of the cone quotient into `k(C)[T]`.
The whole cone fraction field is never identified with the curve function
field. Ungraded evaluation at the normalized coordinates is not injective:
one chosen coordinate is one. An isomorphism between this reduced induced
curve and the alternate scheme `Proj(K[X₀,X₁,X₂]/(F))` has not been proved
and is not silently used.

### The concrete-curve conditional theorem

`PlaneHyperplaneRestriction` proves the same canonical quartic statement
on any nonempty open contained in a standard chart, using restricted
actual frames. This allows a common refinement on which an independently
given theta sheaf is trivial. No trivialization of theta on the three
entire coordinate charts is assumed.

`planeQuintic_even_theta_sections_eq_zero_of_normal_frames` in `PlaneThetaVanishing.lean`
applies to an algebraically closed field and a homogeneous degree-five polynomial with prime principal ideal.
It constructs the actual curve's integrality, and uses the already
constructed `H`, square sheaf `T`, three coordinate sections and
hyperplane square pairing. That pairing's local tensor-perfectness,
quadratic surjectivity and quartic injectivity are proved rather than
supplied. Its remaining inputs
are precisely:

- An actual module sheaf `Θ` and actual natural pairing `μ:Θ×Θ→T`.
- A nonempty affine cover refining the standard coordinate cover, with
  integrally closed coordinate rings, coherent theta frames and bijective
  local tensor lifts of `μ`.
- Even dimension `Even (finrank K Γ(Θ))`.

It proves that every actual global theta section is zero. It requires no
separate hyperplane dimension, finite-dimensionality, quadratic-surjectivity
or quartic-restriction hypothesis. The existence of the normal theta-framed
refinement and specified theta pairing remain genuine assumptions, not
conclusions inferred from naming the curve smooth. The older
`planeQuintic_even_theta_sections_eq_zero` remains as the lower-level
interface with explicit `h2`.

### The actual quadratic-surjectivity proof

`planeCurve_quadraticSectionMap_surjective` proves surjectivity of the
constructed actual restriction map under weaker hypotheses than the theta
theorem: the field is infinite, the equation is homogeneous of total
degree greater than one, and `(F)` is prime. It needs neither smoothness
nor normality. No caller-supplied monicity, coordinate choice or lifting
property remains.

First, `PlaneChartRepresentatives` combines the actual closed immersion's
surjection on affine rings with `Proj.basicOpenIsoAway` and
`HomogeneousLocalization.Away.mk_surjective`. Thus an actual chart function
has a homogeneous fraction representative. `QuadraticFractionBridge`
derives the actual square sheaf's weight-two transition formula.
`PlaneLinearChartRepresentatives` constructs actual regular ratios `Xᵢ/L`
for any nonzero linear form and compares their generic values by an
identity in the actual ambient projective stalk. Using these ratios,
`LinearChartQuadraticSections` glues the actual regular function `s/L²`
on `D(L)`. Its representative yields a homogeneous numerator `A` of degree
`m+2` with generic value `c(s) L(f)^m`. These are conclusions about an
arbitrary actual global square-sheaf section `s`.

Second, `HomogeneousCoordinateChoice` constructs a polynomial coordinate
equivalence and a nonzero scalar normalization making the equation monic
in the last variable. `PlaneMonicModel` gives an actual equivalence of the
multivariate cone quotient with the monic root-adjoining presentation.
Its finite free basis clears compatible powers of the other two
coordinates. `PlaneCoordinateClearing` transports that result back to two
actual linear forms `L₀,L₁` in the original cone. This coordinate change
is used only for algebra: the proof requires no projective automorphism
or sheaf transport.

Third, the full homogeneous kernel converts the two local numerators'
generic compatibility into an equality modulo `(F)`. The proved clearing
property gives a common element of the original cone, and
`LinearDenominatorClearing` projects to its homogeneous degree-two part.
The resulting quadratic polynomial has the given section's actual generic
coefficient. Injectivity of the actual square-sheaf global generic map
then proves equality of the global sections. Thus affine restriction
surjectivity is not used as a substitute for global surjectivity: the
compatibility, clearing, degree extraction and global comparison are all
checked. A separate theorem also handles a defining equation already
monic in the third coordinate.

### What still has to be supplied

The remaining geometric obligations are:

1. Derive the necessary primality and normality from the original smooth
   plane-quintic assumptions. Construct the specified theta module sheaf,
   its coherent local frames and its locally perfect square pairing from
   the geometric square isomorphism, including adjunction identifying the
   canonical sheaf with the constructed hyperplane square. The actual
   hyperplane construction alone does not supply this theta data.
2. Relate the line bundle from the specified real double cover to this theta
   object and its geometric parity, including base change; then construct
   the real symmetric resolution and compare the signed discriminant cover.

The paper proof in §1 remains a proof of the first theta lemma. The checked
conditional theorem covers its section-theoretic logic, including actual
sheaf isomorphism, internally derived dimensions, and parity. The new
geometric constructions remove former existence and generic-coordinate
interfaces, and the new actual section argument discharges quadratic
surjectivity. The theta-data and smoothness-to-normality inputs remain.
The original real conic-bundle existence question and
the later Brauer, quadratic-form, birational, and real-connectedness
implications are still not formally proved.
