# Global trace kernel from a coherent quadratic atlas

This milestone starts with an actual module sheaf `M` on a scheme `X`, not
with a postulated trace-zero line. It does not yet construct `M` from the
specified finite étale discriminant double cover.

## Exact atlas input

`KummerModuleAtlas M U` supplies, on an actual covering family `U`:

1. A section-ring unit `u_i` on each `U_i`.
2. On every subopen `V ≤ U_i`, an actual linear equivalence from `M(V)` to
   `QuadraticAlgebra Γ(X,V) (res u_i) 0`, whose two coordinates commute with
   restriction.
3. Actual algebra isomorphisms between these quadratic models on every
   common subopen, agreeing with the given linear coordinates on `M(V)`.

These are substantive local-model hypotheses. No trace map, trace-zero
line cocycle, line-square isomorphism, or vanishing assertion is a field of
the atlas structure. A global algebra structure on `M` and a comparison
with the algebra sheaf of a specified cover are not constructed here.

## Constructions and checks

- `KummerModuleAtlas.trace` glues the actual local `Algebra.trace` maps.
  `trace_apply` proves its chart formula.
- `traceZeroSheaf` is the categorical kernel of this actual glued morphism.
  `moduleSheafKernelSectionEquiv` identifies sections of a sheaf kernel
  with the linear kernel of the section map, compatibly with inclusion
  and restriction.
- When two is invertible in the section rings, `traceZeroFrame` provides
  restriction-compatible rank-one coordinates on this actual kernel.
- `traceZeroTransition` extracts its unit cocycle, and
  `traceZeroDescentIso` identifies the actual kernel with the descended
  line. `traceZeroTransition_eq` identifies the extracted transition unit
  with the one induced by the supplied algebra change of coordinates.
- `traceZeroSquareIso` constructs the descended square trivialization.
  `traceZeroSquarePairing` is a natural pairing on the actual kernel;
  `traceZeroSquarePairing_tensor_bijective` proves local tensor-perfectness.
  `traceZeroSquarePairing_algebra_mul` proves that inclusion into each
  quadratic model identifies the pairing with actual algebra multiplication.

## Plane-quintic endpoint

`planeQuintic_even_trace_kernel_twist_sections_eq_zero` takes an
algebraically closed field in which two is invertible, a homogeneous quintic
of total degree five with the explicit projective Jacobian condition, an
actual open cover, an actual module sheaf with the atlas above, and even
finrank of the constructed twist's global sections.

Invertibility of two in every section ring is derived by pulling back base
field constants. The trace, its kernel, line coordinates, square
trivialization, and hyperplane twist are constructed internally.
`planeTraceZeroThetaHomEquiv` proves the tensor universal property for
pairings on the actual kernel and actual hyperplane sheaf.
`planeTraceZeroThetaCotangentSquareIso` constructs the square comparison
with the actual relative differential sheaf. The endpoint proves that
each global section of the twist is zero; finite-dimensionality is derived
by the existing section argument, not separately assumed.

## Remaining geometric obligations

The following are still unproved:

- Construct the module sheaf and this atlas from the specified finite
  étale discriminant double cover, including the local unit parameters.
- Identify the glued trace with the trace of that cover's actual pushforward
  algebra sheaf, and hence this kernel with its actual trace-zero summand.
- Identify the constructed twist with the theta characteristic specified
  in the original question and derive the required parity after base change.
- Formalize the original real conic bundle and the real-topological argument,
  including the number of connected components.

Thus the atlas-relative kernel/descent identification is now proved, but
the discriminant-cover-relative identification remains open. Neither the
existence nor the nonexistence statement of the original problem follows
from the checked endpoint alone.

## Subsequent local algebra construction

[BASED_UNRAMIFIED_QUADRATIC_MODEL.md](BASED_UNRAMIFIED_QUADRATIC_MODEL.md)
constructs unit Kummer models and actual trace-kernel multiplication
tensor squares from an actual basis (1,e), invertibility of two and
formal unramifiedness. This removes the unit-model hypothesis at the
based-algebra level. Constructing compatible local bases for the specified
cover and assembling their restriction-compatible atlas are still open.
