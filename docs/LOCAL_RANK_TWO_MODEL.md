# Local rank-two model without a supplied basis

The checked endpoint is `exists_unit_kummer_model_of_local_finite_flat`
in `EvenQuinticConic/LocalRankTwoKummer.lean`.

Its exact inputs are commutative rings R and A with an R-algebra structure,
`IsLocalRing R`, `Invertible (2 : R)`, `Module.Finite R A`,
`Module.Flat R A`, `Algebra.FormallyUnramified R A`, and
`Module.finrank R A = 2`. Its conclusion is

```lean
∃ u : Rˣ, Nonempty (A ≃ₐ[R] KummerAlgebra (u : R))
```

No basis, presentation, unit parameter, or Kummer isomorphism is supplied.
Mathlib's `Module.free_of_flat_of_isLocalRing` first gives freeness;
`Module.finBasisOfFinrankEq` gives an arbitrary two-element basis.
`RankTwoUnitBasis.lean` computes Tr(1)=2 and applies the trace to the
basis expansion of 1. As two is a unit, the local-ring unit-sum property
forces one of the coordinates of 1 to be a unit. A permutation and an
explicit invertible triangular linear map yield a basis (1,e).
The earlier based unramified model then supplies the Kummer equivalence.

Two further endpoints concern the original algebra trace:

- `nonempty_trace_kernel_coordinate_of_local_finite_flat` constructs
  a linear equivalence `LinearMap.ker (Algebra.trace R A) ≃ₗ[R] R`.
- `exists_trace_kernel_tensor_equiv_of_local_finite_flat` constructs
  a linear equivalence from the tensor square of that kernel to R,
  and proves for all kernel elements x,y that their product in A is
  the image under `algebraMap R A` of the tensor-equivalence value.

These conclusions use the actual mathlib algebra trace, not a custom
predicate asserting a line bundle or a square isomorphism.

## Remaining scope

This module establishes the local-ring result. The subsequent
`PrincipalOpenKummer` module now constructs a principal-open cover with
unit Kummer models under module finite presentation, flatness, formal
unramifiedness, invertibility of two and pointwise rank two; see
[PRINCIPAL_OPEN_KUMMER.md](PRINCIPAL_OPEN_KUMMER.md). It does not yet assemble
a restriction-compatible module-sheaf atlas or identify a specified
cover's pushforward trace. The global theta endpoint still requires its
coherent atlas and parity inputs. No original geometric conclusion follows yet.
