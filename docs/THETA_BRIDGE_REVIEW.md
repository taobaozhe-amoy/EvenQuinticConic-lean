# The theta-characteristic bridge: mathematical proof and exact interfaces

This note supplies a mathematical proof of the first geometric lemma in the
proposed argument. It is not a claim that the complete geometric theorem has
been checked by Lean. The polynomial factorization used below is formalized;
the curve, sheaf-cohomology, generic-section and divisor constructions below
are not supplied by those polynomial theorems.

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

## 4. Formalization boundary and useful next targets

The existing polynomial theorems establish the homogeneous factorization
once their algebraic hypotheses hold. The coefficient construction is now formalized in `GradedRestriction` and
`WeightedRestriction`, and the finite-degree variant in
`FiniteDegreeRestriction`. `GenericCoefficientModel` proves the ratio identity.
`LocalSquareUnit` proves the integrally-closed local-ring step, including
weighted quotients. These are genuine algebraic theorems, but their inputs
have not yet been constructed from the actual curve and sheaves.

The following geometry has not been formalized merely by writing this note:

1. The actual smooth projective plane curve and its sheaves `O_C(n)`.
2. The two restriction-map facts in §1 and multiplication compatibility.
3. Injection from global line-bundle sections into the generic fiber.
4. The actual divisor or local-ring reconstruction of a line-bundle
   isomorphism from `psi(s²)=c a²`.
5. The interpretation of parity and the real base-change statement.
6. The symmetric resolution and its identification with the specified cover.

The weighted generic model is a convenient algebraic intermediate theorem.
For the eventual geometry bridge, the finite-degree restriction formulation
is weaker and sufficient: there is no need to prove every graded kernel
piece just to obtain `AD=B²`.

The proof above validates the first theta lemma mathematically. It does not
settle the original existence question for real conic bundles, and it gives
no reason by itself to reject a purported real example.
