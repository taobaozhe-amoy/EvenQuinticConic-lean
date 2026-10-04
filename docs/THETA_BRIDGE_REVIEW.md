# The theta-characteristic bridge: mathematical proof and exact interfaces

This note supplies a mathematical proof of the first geometric lemma in the
proposed argument. It is not a claim that the complete geometric theorem has
been checked by Lean. The section-theoretic implication is now formalized for actual schemes and
module sheaves under explicit geometric inputs, including an actual
quadratic-section map and its surjectivity. The specific smooth plane
quintic has not yet been shown to supply all of those inputs. Sections 4–5
state the checked implication and the remaining instantiation work.

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

## 5. Remaining geometric instantiation

The conditional theorem above is not yet the theorem for all smooth plane
quintics. Its outstanding geometric inputs are:

1. Construct the particular curve as an actual scheme over the base field,
   its twist sheaves `O_C(1),O_C(2)`, and the theta sheaf. Construct the
   natural pairings from the specified tensor-square isomorphism and verify
   their local tensor-perfectness.
2. Derive a normal affine trivializing cover and coherent frames from that
   geometry. Smoothness of the given plane quintic has not yet been used to
   discharge these hypotheses in the final Lean theorem.
3. Prove that its homogeneous coordinate sections make the explicitly
   constructed `quadraticSectionMap` surjective. The projective-space
   cohomology/restriction theorem providing this has not yet been formalized
   in this project.
4. Identify the actual generic coefficients of its coordinate sections with
   the proved algebraic chart model, thereby supplying `h4`.
5. Relate the line bundle from the specified real double cover to the actual
   theta object and its geometric parity, including the real base change;
   then construct the real symmetric resolution and compare the signed
   discriminant cover.

`PlaneQuintic.lean` makes item 5 more concrete. It constructs the homogeneous
principal ideal, a genuine `ProjectiveSpectrum` vanishing locus and generic
point, and the affine-cone quotient `K[X₀,X₁,X₂]/(F)`. Evaluation into that
quotient's fraction field has exactly the principal ideal as kernel. After
normalizing by a nonzero coordinate, the homogeneous degree-below-five
injectivity theorem still holds, giving quartic injectivity.

These coordinates still live in the **cone's fraction field**. The code
does not equate it with the curve's actual generic stalk or silently identify
its normalized coordinates with `schemeGenericLinearMap` for the geometric
hyperplane sheaf. Nor is ungraded evaluation at normalized coordinates
injective: the chosen normalized coordinate equals one. Connecting this
degree-zero coordinate model to the actual `Spec`/`Proj` curve and twist
sheaves is an outstanding step. The whole cone fraction field cannot be
identified with the curve's function field; only the appropriate normalized
coordinate data are intended to be compared.

The paper proof in §1 remains a proof of the first theta lemma. The checked
conditional theorem now covers its section-theoretic logic, including the
actual sheaf isomorphism and parity step, once the listed geometric inputs
are supplied. The original real conic-bundle existence question and the
later Brauer, quadratic-form, birational, and real-connectedness implications
are still not formally proved.
