# Unit Kummer models from an actual based unramified algebra

This milestone constructs a local quadratic model from an actual algebra
and its basis. It does not assume the desired Kummer parameter is a unit,
and does not replace formal unramifiedness with a custom predicate.

## Exact input and result

Let R and A be commutative rings, with an actual R-algebra structure on A.
The inputs are:

- An actual basis `v : Module.Basis (Fin 2) R A` with `v 0 = 1`.
- Invertibility of `2 : R`.
- mathlib's `Algebra.FormallyUnramified R A`.

`exists_unit_kummer_model_of_basis` constructs a unit `u : Rˣ` and an
actual R-algebra isomorphism `A ≃ₐ[R] QuadraticAlgebra R (u : R) 0`.
Formal unramifiedness is enough; in particular this applies when the
corresponding étale algebra instance is available.

The basis is a substantive input. This is not yet a theorem constructing
such bases on a Zariski cover of every finite étale rank-two algebra.

## Multiplication coefficients and completing the square

Put e = v(1). Read a and b from the actual basis coordinates of e*e.
`quadraticBasis_generator_square` proves e*e = a + b*e, and
`quadraticBasisAlgEquiv` constructs the algebra isomorphism from
`QuadraticAlgebra R a b` to A. The multiplication law is proved from basis
expansion, not assumed as an additional equation.

For c = b/2, translating the generator by c gives t*t = u where
u = a + c*c. `quadraticShiftEquiv` and `quadraticNormalForm` construct the
actual algebra equivalences. `quadraticCenteredParameter_discriminant`
checks 4*u = b*b + 4*a.

## Why the parameter is a unit

`kummer_isUnit_of_formallyUnramified` proves the key implication for an
arbitrary parameter u, even without assuming two invertible in this lemma.

Let B = QuadraticAlgebra R u 0 and Q = R/(u). There is an actual algebra
map B → Q sending r + s*t to the class of r. Use it to make Q a B-module.
The map d(r + s*t) = class(s) is an R-derivation: its Leibniz rule follows
from the actual multiplication formula. Formal unramifiedness says that
the actual Kähler differential module is zero, so its universal property
forces d = 0. Since d(t) = 1 in Q, the quotient is the zero ring. Thus
1 belongs to (u), and u is a unit.

Transporting formal unramifiedness through the completed-square
isomorphism proves `quadraticCenteredParameter_isUnit`. No nondegenerate
trace pairing or invertible discriminant is supplied as an input.

## The actual trace kernel and multiplication

`algebraTraceKernelKummerEquiv` restricts the actual algebra isomorphism to
kernels of the actual `Algebra.trace`, using trace invariance.
`algebraTraceKernelTensorEquiv` constructs a linear equivalence

```
ker(Algebra.trace R A) ⊗[R] ker(Algebra.trace R A) ≃ₗ[R] R.
```

`algebraTraceKernelTensorEquiv_mul` proves that including trace-zero
vectors into A identifies this map with multiplication in A.
`exists_trace_kernel_tensor_equiv_of_basis` constructs this equivalence
and proves its multiplication formula directly from the basis and formal
unramifiedness inputs above. A kernel-square equivalence is not an input.

## Remaining connection to the geometric problem

The earlier atlas-relative global trace construction remains unchanged.
The new algebraic theorem supplies a unit model once an actual based
unramified algebra is provided. Still required:

1. Construct suitable local bases beginning with one for the specified
   finite étale double cover's pushforward algebra.
2. Prove the resulting local coordinates commute with restriction and
   construct the actual overlap maps, thereby building `KummerModuleAtlas`.
3. Identify its glued trace with the trace of the specified pushforward
   algebra sheaf, and identify the resulting theta twist and its parity.
4. Complete the real base-change and real-topological arguments.

The original real conic-bundle existence/nonexistence question is not
settled by this milestone.
