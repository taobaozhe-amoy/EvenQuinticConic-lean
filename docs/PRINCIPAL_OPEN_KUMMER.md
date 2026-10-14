# Principal-open Kummer models

The endpoint `exists_principal_unit_kummer_cover` in
`EvenQuinticConic/PrincipalOpenKummer.lean` has these exact inputs:

- Commutative rings R and A and an actual R-algebra structure.
- `Module.FinitePresentation R A` and `Module.Flat R A`.
- `Algebra.FormallyUnramified R A` and `Invertible (2 : R)`.
- For every prime p of R, `Module.finrank Rₚ (Rₚ ⊗[R] A) = 2`.

It constructs a function f from `PrimeSpectrum R` to R such that
`⨆ p, PrimeSpectrum.basicOpen (f p) = ⊤`. For every p it constructs a unit
u in `Localization.Away (f p)` and an actual algebra equivalence

```lean
(Localization.Away (f p) ⊗[R] A) ≃ₐ[Localization.Away (f p)]
  KummerAlgebra (u : Localization.Away (f p))
```

The intermediate `exists_principal_unit_kummer_model_atPrime` uses only
rank two at a single prime and returns r outside that prime.
`exists_principal_rankTwo_basis` spreads a rank-two basis at an arbitrary
multiplicative localization to one principal localization; its resulting
basis is on the actual tensor-product base-change algebra.

## Proof

Over the local ring Rₚ, finite flatness gives a free module; the rank
hypothesis supplies a two-element basis. Mathlib's finite-presentation
basis-spreading theorem gives a basis after inverting one r outside p.
The canonical localized-module/tensor-product equivalence transports it
to the base-change algebra.

The new `RankTwoUnimodularBasis` module removes the need for the principal
localization itself to be a local ring. In a basis v, write 1=a v₀+b v₁
and set c=Tr(v₀)/2, d=Tr(v₁)/2. The trace identity Tr(1)=2 gives ac+bd=1.
The matrix with columns (a,b) and (-d,c) has determinant one; its explicit
inverse gives an actual basis beginning with 1. The earlier quadratic
model and formal-unramifiedness argument then give a unit Kummer parameter.
Formal unramifiedness and invertibility of two are transported to the
base-change algebra/base ring internally. Choosing r at every prime gives
a genuine cover: each p belongs to its own D(r).

## Exact boundary

Finite presentation here is **module** finite presentation and remains an
explicit input. The conclusion gives algebra models on principal
localizations and proves their basic opens cover Spec R. It does not yet
identify these rings with the required structure-sheaf sections, extend
the models to all subopens, or prove the restrictions and overlap laws
required by `KummerModuleAtlas`. It also does not extract the algebra or
these hypotheses from the specified discriminant cover. Thus the full
geometric existence/nonexistence question remains open in this project.
