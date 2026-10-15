# Multiplicative charts and trace on the original scheme morphism

The previous affine-presentation transport gap is now closed under the
explicit hypotheses below. The construction takes the actual morphism
`f : X ⟶ Y`; it does not take a Kummer chart, atlas, trace, trace-zero line,
or multiplication-square identification as input.

## Exact geometric inputs

- `IsFinite f`, `IsEtale f` and explicit `AlgebraicGeometry.Flat f`.
- An actual affine open cover `U : ι → Y.Opens` with `iSup U = ⊤`.
- Noetherian section rings `Γ(Y,U i)` and invertibility of 2 in each.
- For the actual algebra structure induced by `f.app (U i)`, the module
  `R_p ⊗[R] Γ(X,f⁻¹U i)` has finrank two at every prime of `R=Γ(Y,U i)`.

These assumptions are not yet instantiated for the original problem's
specified discriminant cover. Flatness remains explicit because the
pinned mathlib development does not supply the required scheme
étale-to-flat implication here. The mathematical implication is not in doubt.

## Transport preserves actual multiplication

`KummerScalarEquiv` transports the two coefficients through an actual ring
isomorphism, with matching quadratic parameters.
`PushforwardKummerChart.sourceIso` uses the inverse of the source scheme
isomorphism's actual map on sections. `baseIso` uses the base isomorphism,
the corresponding equality of source opens and the coefficient-ring
equivalence. Both preserve actual coefficients and every restriction map.

`PushforwardKummerChart.isoTransport` combines these constructions for a
commuting isomorphism of scheme arrows. `openImage` then transports a
multiplicative chart of `f|_U` to a chart of the original f on an image
open. These are ring equivalences throughout, not only linear comparisons.

## Global covering charts, without supplied charts

`exists_restrictedAffinePushforwardKummerCharts` starts with the already
proved principal-localization models of the actual section algebra,
constructs affine pushforward charts, and transports them through the
canonical `isoSpec` presentation to the actual restricted morphism.

`exists_schemePushforwardKummerCharts_of_affine_cover` then constructs
covering multiplicative charts on Y for f itself. Its index set is
`Σ i, PrimeSpectrum Γ(Y,U i)`. Image-cover and dependent-union lemmas
prove coverage, including empty opens. Comparisons through the same
actual source section rings produce all cross-chart algebra maps.

`exists_schemePushforwardKummerAtlas_of_affine_cover` obtains the actual
module atlas of `f_* O_X` from this stronger multiplicative result.

## Unique sheaf trace and actual kernel

`existsUnique_schemeFiniteEtaleTrace` proves existence and uniqueness of
the actual module-sheaf morphism agreeing with the algebra trace in every
multiplicative chart of f. `schemeFiniteEtaleTrace` chooses that unique
morphism, and `schemeFiniteEtaleTrace_eq_atlas` identifies it with the
trace from any covering family of actual multiplicative charts.

This is a sheaf trace. No assertion identifies it with the algebra trace
of the global-section algebra on an arbitrary nonaffine open, where the
section module need not be finite projective.

`schemeFiniteEtaleTraceZeroSheaf` is its actual categorical kernel.
`exists_schemeFiniteEtaleTraceZeroFrames` constructs coherent rank-one
frames on a cover. Invertibility of 2 on arbitrary opens is derived from
the supplied affine cover using actual restriction maps and the sheaf
criterion for units; it is not an additional hypothesis.

`exists_schemeFiniteEtaleTraceZeroSquarePairing` constructs a natural
pairing of this kernel with itself into the structure module. On every
subopen of the constructed cover, its tensor linear map is bijective.
The proof also establishes, with the actual kernel inclusion `j`,

```
f.app V (P.app V s t) = j_V(s) * j_V(t)
```

in the original ring `Γ(X,f⁻¹V)`. Thus the square pairing is identified
with actual multiplication, rather than an unrelated abstract form.

## Remaining original-problem obligations

The generic transport and atlas construction are complete at the stated
hypothesis boundary. Still required are the specified discriminant cover
and its geometric/rank hypotheses, identification with the specified
theta characteristic, parity and real base change, and the remaining
real geometry and connectedness argument. The original real conic-bundle
existence/nonexistence problem is still not proved.
