# Actual pushforwards, open restrictions, and affine presentations

This increment supplies parts of the bridge from the proved affine Kummer
atlas to a cover over a general base scheme. It does not yet construct the
full atlas of the specified discriminant cover.

## Restricting the actual morphism

For every scheme morphism `f : X ⟶ Y` and base open `U`,
`schemePushforwardRestrictionIso` constructs an actual module-sheaf isomorphism

```
(f_* O_X)|_U ≅ (f|_U)_* O_(f⁻¹U).
```

The maps on sections are ring equivalences induced by the equality of the
two corresponding opens in X. The proof checks compatibility with both
the actual structure-map coefficients and all restriction maps. No affine,
finite, flat or étale hypothesis is needed for this comparison.

`KummerModuleChart.openImage` and `KummerModuleAtlas.openImage` transport an
atlas on an actual open subscheme back to the corresponding image opens
of the original scheme. They transport the parameters, coordinates,
restriction identities and algebra overlap maps together.
`schemePushforwardAtlasOpenImage` combines this with the canonical
pushforward restriction isomorphism. The image opens cover U; a separate
Sigma-indexed cover lemma handles a covering family of such base opens.

These are transport theorems for a supplied atlas. A general module-sheaf
isomorphism alone does not assert compatibility with an independently
given multiplication. The ring-level comparison above is explicit, and
the multiplicative chart interface below keeps this distinction visible.

## Actual multiplicative charts and their trace

`PushforwardKummerChart f U u` records ring equivalences

```
Γ(f⁻¹V, O_X) ≃+* Γ(V, O_Y)[t]/(t²-u|_V),  for every V ⊆ U,
```

together with their compatibility with `f.app V` and the actual
restriction maps. It does not postulate a trace or a trace-zero line.
`pushforwardKummerAtlas` constructs all overlap algebra equivalences by
comparing through the same source section ring. No cross-chart
compatibility is an additional input.

The previously proved principal affine models populate this stronger
interface in `affinePushforwardRingChart`, without new chart assumptions.
The resulting global trace agrees with every other multiplicative chart
of the same morphism (`pushforwardKummerAtlas_trace_on_chart`). Two full
families of multiplicative charts give equal global trace morphisms
(`pushforwardKummerAtlas_trace_independent`), without supplied comparison
maps between the two families.

## Affine presentations from geometric hypotheses

For an affine morphism and an affine base open U,
`affinePreimageArrowIso` identifies the actual restricted arrow with
`Spec.map (f.app U)`, using the canonical affine-open scheme isomorphisms.
Both commuting squares are proved.

`exists_affinePreimageKummerModels` obtains a principal-open cover and actual
localized algebra isomorphisms for the section algebra `Γ(X,f⁻¹U)` over
`Γ(Y,U)`. `exists_affinePreimageKummerAtlas` constructs the actual module
atlas from these multiplicative models. Their inputs are:

- `IsFinite f` and `IsEtale f`;
- geometric `AlgebraicGeometry.Flat f`;
- an affine U with Noetherian section ring;
- invertibility of 2 in that section ring;
- rank two at every prime of that section ring.

Module finiteness follows from geometric finiteness; the Noetherian
assumption gives module finite presentation. Geometric flatness and
étaleness give the algebra's flatness and formal unramifiedness. The
conclusion is an actual pushforward atlas on `Spec Γ(Y,U)`, and does not
yet silently identify that base with the original open subscheme.

Flatness is retained explicitly: the pinned mathlib version does not
provide the needed scheme étale-to-flat implication here. This is a
formalization gap, not an assertion that étale morphisms fail to be flat.

## Remaining bridge

The next step is to transport the multiplicative affine charts through
the canonical affine presentation isomorphisms, retaining their scalar
and restriction laws, then combine them over a cover of the original
base. Instantiate the geometric and rank hypotheses for the specified
discriminant cover and identify its trace-zero line and theta twist.
Theta parity, real base change and real topology remain unfinished.

The original real conic-bundle existence/nonexistence question is not
proved by this increment.
