# Local quadratic multiplication and the theta twist

This milestone constructs a square trivialization from local quadratic-algebra
multiplication. It does **not** construct those local models from a specified
finite étale discriminant cover, nor settle the real conic-bundle question.

## Actual local algebra and actual trace kernel

`KummerAlgebra u` is mathlib's `QuadraticAlgebra R u 0`, with its actual
commutative `R`-algebra structure and generator `t` satisfying `t*t=u`.
`kummer_trace` computes the actual `Algebra.trace`: `Tr(x)=2*x.re`.
`KummerTraceZero u` is the kernel of that linear map, not a replacement
predicate or a separately stipulated rank-one module.

When `2` is invertible, `kummerTraceZeroCoordinate` constructs an `R`-linear
isomorphism from this kernel to `R`, sending `a*t` to `a`. When `u` is also
a unit, `kummerTraceZeroTensorEquiv` constructs

```
KummerTraceZero u ⊗[R] KummerTraceZero u ≃ₗ[R] R.
```

`kummerTraceZeroTensorEquiv_mul` proves that this tensor isomorphism is the
actual algebra multiplication followed by identification of the scalar
subalgebra. Thus tensor-perfectness is derived from the two unit hypotheses.

## Actual changes of algebra charts

For an actual `R`-algebra isomorphism `e : B(u) ≃ₐ[R] B(v)`:

- Trace invariance forces `e(t_u)=c*t_v` when `2` is invertible.
- The inverse algebra map supplies the inverse of `c`; `kummerChangeUnit e`
  constructs that unit.
- Preservation of multiplication proves `u=v*c*c`.
- `kummerChangeUnit_trans` proves the composition law for these units.
- `kummerTraceZeroMapEquiv` restricts the actual algebra isomorphism to the
  actual trace kernels. Its coordinate transformation is the constructed unit.

These statements are proved for actual algebras and maps. They do not yet
extract a Zariski atlas of this form from a finite locally free étale algebra.

## Descent on the actual scheme

For a given line cocycle `g` on a cover `U`, choose actual section-ring units
`u_i`. On any common subopen, assume actual algebra homomorphisms

```
B(res(u_j)) →ₐ[Γ(X,V)] B(res(u_i))
```

that send the source generator to `g_ij` times the target generator. The input
`KummerOverlapCoordinates` records precisely this compatibility with the
**given** line coordinates. Algebra multiplication then proves

```
res(u_j) = res(u_i) * g_ij * g_ij.
```

The coefficient identity is not an additional hypothesis of
`squareIsoOfKummerMaps`. The lower-level `squareIsoOfLocalUnits` glues these
local multiplication coefficients into the actual isomorphism

```
(g.mul g).moduleSheaf ≅ SheafOfModules.unit X.ringCatSheaf.
```

`squareIsoOfLocalUnits_apply` checks that the glued morphism multiplies each
square coordinate by exactly the specified `res(u_i)`. The construction uses
actual structure-sheaf restrictions and works on arbitrary covering families.

## Endpoint and remaining obligations

`planeQuintic_even_kummer_twist_sections_eq_zero` takes:

1. An algebraically closed field, a homogeneous degree-five equation, and
   the explicit projective Jacobian condition.
2. An actual open cover and actual unit line cocycle.
3. Actual local units, quadratic-algebra overlap maps, and their agreement
   with the given line generator coordinates.
4. Even finrank of the constructed hyperplane twist's actual global sections.

It constructs the line-square trivialization, the hyperplane twist, and its
cotangent-square isomorphism internally, then proves every global section is
zero. Finite-dimensionality is derived by the existing section argument.

Still unproved: the passage from the **specified** finite étale discriminant
double cover to these local algebras, their restriction-compatible chart maps,
and the actual global trace-zero sheaf; identification of its descended
cocycle with the input line data; the geometric parity and real base-change
steps; the final real-geometric and connectedness argument. This milestone
does not claim an étaleness criterion or the existence of local Kummer models
for every rank-two étale algebra.

## Subsequent atlas-relative extension

[GLOBAL_TRACE_KERNEL_BRIDGE.md](GLOBAL_TRACE_KERNEL_BRIDGE.md) removes the
independently supplied line cocycle when an actual module sheaf with a
restriction-compatible quadratic atlas is given. It constructs the global
trace, its actual kernel, the kernel/descent identification and square
pairing internally. The specified-cover-to-atlas step remains open.
