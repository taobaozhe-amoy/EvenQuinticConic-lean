# The theta-characteristic bridge: mathematical proof and exact interfaces

This note supplies a mathematical proof of the first geometric lemma in the
proposed argument. It is not a claim that the complete geometric theorem has
been checked by Lean. The polynomial factorization used below is formalized;
the specific curve, its sheaf-cohomology and generic-section constructions
below are not supplied by those polynomial theorems. The local-to-global
reconstruction now has a checked theorem for actual module sheaves with
explicit coherent frames and rational coefficient data; §4 states exactly
which geometric inputs are still missing.

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

## 4. Formalized local-to-global reconstruction

The homogeneous polynomial factorization is proved in the existing
polynomial modules. `GradedRestriction`, `WeightedRestriction`, and
`FiniteDegreeRestriction` supply the coefficient constructions and the
finite-degree version of the restriction argument.
`GenericCoefficientModel` proves the weighted rational ratio identity.
The following subsequent steps now use actual schemes and sheaves.

### Actual functions and local extension

For `X : Scheme [IsIntegral X]`, `GenericPointInjection` uses the actual
structure sheaf, actual restrictions, and `X.functionField`, defined by
mathlib as the stalk at the generic point. Its equality tests use the proved
injectivity of the actual map `Γ(X,U) → X.functionField` for nonempty `U`.

On a nonempty affine open `U`, with the explicit assumption
`IsIntegrallyClosed Γ(X,U)`, the theorem
`existsUnique_regular_unit_of_generic_sq_ratio` proves

```
germ(u) r² = germ(v) q²,  q ≠ 0,  u,v ∈ Γ(X,U)ˣ
  ⇒ ∃! w ∈ Γ(X,U)ˣ,  germ(w)=r/q and u w²=v.
```

This uses the actual identification of the function field as the fraction
field of the affine coordinate ring. It does not assume that `q` is a unit
of that coordinate ring, so simultaneous vanishing of local numerator and
denominator has not been excluded.

`SheafGluing` then gives unique gluing of actual regular representatives of
one rational function, and gluing of unit representatives to a unit. It
also proves that a morphism of actual sheaves is bijective on every open
once it is bijective on every subopen of each member of a covering family.
Existence comes from the sheaf condition; agreement on overlaps is proved,
not replaced with an assumed gluing conclusion.

### Generic coefficients of actual module-sheaf sections

`moduleGenericCoefficient_injective` in `ModuleGenericInjection.lean` is now proved
for an actual module sheaf `M : X.Modules` on an integral scheme, with a
cover by coherent rank-one frames. Choose a frame on any nonempty open
`V`; restrict a global section to `V`, take its coordinate, and map that
regular function to `X.functionField`. Equality of these generic
coefficients forces equality on `V`, then on every framed covering open
through their nonempty overlaps, and finally globally by the sheaf
condition. The proof does not assume generic injectivity as a premise.

The corresponding construction `moduleGlobalGenericLinearMap` uses the
actual module `M.val.obj (op ⊤)` of global sections. It is linear over
`Γ(X,⊤)`, with the canonical scalar action on `X.functionField`, and is
injective under the same covering hypotheses. This supplies the general
section-to-generic-coefficient step. Instantiating it for `theta` and `H`, supplying their compatible actions of
the specified base field, and proving the geometric product identities
remain to be done.

### Coherent frames and a module-sheaf isomorphism

`SheafTrivialization` constructs the actual morphism `O_X → M` given by
`r ↦ r • s`, for a compatible section `s` of an actual sheaf of modules.
When its local coordinates are units, the morphism is bijective on local
sections and hence gives an actual isomorphism of module sheaves.

`ModuleSheafFrame`, defined in `LocalFrames.lean`, consists of linear equivalences

```
M(V) ≃ Γ(X,V),  for every V ⊆ U,
```

compatible with the actual restriction maps. Thus it is legitimate local
frame data, with no global trivialization built into its definition. A unit
coordinate on `U` remains a unit on all its subopens. Actual compatible
local sections with unit coordinates glue to a global generator, and the
resulting morphism gives `O_X ≅ M`.

The theorem `exists_global_generator_of_rational_frame_powers` in
`RationalSectionFrames.lean` joins local extension and these module-sheaf constructions. More precisely,
the input is:

1. An actual integral scheme `X` and an actual module sheaf `M : X.Modules`.
2. A cover by nonempty affine opens `U_i` whose actual rings `Γ(X,U_i)` are
   integrally closed, with coherent frames `e_i` for `M`.
3. Rational coefficients `r_i ∈ X.functionField` satisfying
   `r_i = germ(g_ij) r_j`, where on `W=U_i∩U_j` the transition coefficient is
   the **computed** element `g_ij = e_i,W(e_j,W⁻¹(1))` of `Γ(X,W)`.
4. A positive integer `n` and actual units `u_i ∈ Γ(X,U_i)ˣ` such that
   `r_i^n = germ(u_i)`.

The theorem constructs regular units `w_i` with generic value `r_i`, sets
`t_i=e_i⁻¹(w_i)`, and proves their overlap equality by applying a frame and
then the injective actual generic map. The actual sheaf condition produces
a global generator and an isomorphism `O_X ≅ M`. The positive-power condition
can be applied with `n=2` in the intended theta argument.

The direct theorem
`exists_global_generator_of_rational_frame_square_ratios` matches the
weighted theta identity more closely. On the same normal affine framed
cover, suppose `a_i,b_i ∈ Γ(X,U_i)ˣ`, `x_i,y_i ∈ X.functionField`, and

```
y_i ≠ 0,   germ(a_i) x_i² = germ(b_i) y_i².
```

Assume the quotients `x_i/y_i` transform by the computed frame transitions.
The theorem constructs local units `w_i` with

```
germ(w_i)=x_i/y_i,   a_i w_i²=b_i,
```

then actual compatible sections, a global generator, and an actual
isomorphism `O_X ≅ M`. It does not require `y_i` to be a unit of the affine
coordinate ring, and therefore also applies when chosen regular numerators
and denominators vanish at the same point.

The rational coefficients in these theorems are explicit scalar data with
transition identities. They have **not yet been constructed from the
actual generic fiber of a specified theta sheaf**. Supplying these inputs
for `M=theta⊗H⁻¹` is still required; the theorem does not silently supply
that geometric construction.

### Assumption audit

The nonempty-open hypotheses above have a precise role: every nonempty open
of an integral scheme contains its generic point. Pairwise intersections
therefore contain it too, so comparisons in the actual function field are
valid. Empty opens are not mapped into that field. They are handled by the
ordinary sheaf restriction and gluing statements; in the coherent-frame
argument, unit coordinates restrict to every subopen, including the empty
open. Each covering statement still contains the actual condition that the
union is the relevant open or the whole space. Invertibility is not inferred
from a zero ring pretending to have an injective map to a field.

Integral and integrally closed are distinct assumptions here. Integrality
supplies the generic point, the function field, and injectivity. The local
root-extension theorem separately requires integrally closed affine
coordinate rings. None of these results has yet derived those hypotheses
from the smoothness of a particular plane quintic.

## 5. Remaining geometry

The following obligations are not discharged by the reconstruction theorem:

1. Construct the actual smooth plane quintic, its twist sheaves `O_C(n)`,
   the theta sheaf, and the specified tensor-square isomorphism.
2. Prove the degree-two surjectivity and degree-four injectivity of the
   relevant restriction maps, together with multiplication compatibility.
3. Instantiate the proved generic coefficient construction for those line
   bundles, supply the compatible base-field scalar actions, and connect
   it to the geometric product identities and independence hypotheses.
4. Supply a normal affine trivializing cover, coherent frames, rational
   coefficients for the actual section `s/a`, and the transition and
   power-unit identities required by the checked reconstruction theorem.
5. Relate the resulting isomorphism `O_C ≅ theta⊗H⁻¹` to `theta ≅ H`, and
   prove the dimension, parity, and real base-change statements.
6. Construct the real symmetric resolution and compare its signed
   discriminant cover with the specified cover.

The finite-degree restriction formulation remains the smaller sufficient
input: the complete graded-kernel calculation is unnecessary merely to
obtain `AD=B²`. The divisor route in §1 is a mathematical alternative; the
new formalization follows the local-unit and sheaf route and does not claim
to have formalized divisor theory for this curve.

The proof in §1 concerns the first theta lemma. The checked local-to-global
reconstruction strengthens the formalization of that argument but does not
settle the original existence question for real conic bundles. The later
Brauer, quadratic-form, birational, and real-connectedness arguments still
need both mathematical and formal verification.

The corollary `module_generic_coefficients_linearIndependent` additionally
restricts scalars to a field `K` under explicit compatible algebra/module
structures and scalar-tower hypotheses. It proves that a `K`-linearly
independent family of actual global sections has `K`-linearly independent
generic coefficients. Constructing those scalar structures for the specified
theta sheaf remains part of its geometric application.
