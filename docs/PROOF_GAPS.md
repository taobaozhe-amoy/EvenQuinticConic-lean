# Proof obligations that remain open in this project

The following is a work plan for scrutinizing a proposed mathematical argument, not a list of verified consequences. Every implication below needs both a precise statement and a proof. Finding a missing hypothesis or a false implication would require revising the argument, not adding an axiom to Lean.

## 1. State the geometric problem

Define the real base, the smooth projective total space, the conic-bundle morphism, geometric standardness, the smooth discriminant curve of degree five, its étale double cover, and the associated theta characteristic. Define evenness using the parity of the actual dimension of global sections after the appropriate base change. Relate the topology on real points to the intended real algebraic variety.

None of these objects is currently packaged into a Lean statement of the target theorem. Generic propositions named `EvenTheta` or `Rational` would not accomplish this task.

## 2. Even theta and symmetric determinantal representation

The proposed argument first aims to show that an even theta characteristic on a smooth plane quintic is ineffective. The intended route lifts products of sections to conics `A,B,D`, uses the relation `A D - B²` in the principal ideal of the quintic, and then analyzes factorization and line bundles.

The algebraic classification is now proved, including homogeneity. The theorem
`nonproportional_homogeneous_conics_from_quintic_ideal` combines
`PolynomialDegree.lean`, `RankOneFactorization.lean`, `ConicClassification.lean`,
and `HomogeneousConics.lean`: if `deg F=5`, the conics are homogeneous of
degree two, `A,D` are nonzero and not scalar multiples, and `A D-B² ∈ (F)`,
then `A=c a²`, `B=c ab`, `D=c b²` with `c≠0` and homogeneous linear `a,b`.
This works over an arbitrary field and uses actual multivariate polynomials.

`IndependentSquares.lean` also proves that over an algebraically closed field,
two linearly independent elements of a domain algebra have linearly independent
squares. This supplies the abstract algebraic nonproportionality criterion.
It still requires realizing the actual line-bundle sections and their products
in a suitable domain algebra and relating the polynomial lifts to them.

`RestrictionModel.lean` joins these results through an actual algebra
homomorphism `φ : K[σ] →ₐ[K] R`. Given `ker φ=(F)`, independent `s,t`, and
images `φ(A)=s²`, `φ(B)=st`, `φ(D)=t²`, it derives the ideal relation,
nonzero diagonal entries, and their nonproportionality internally, then proves
the homogeneous factorization. This does not construct that model for the
geometric sections; compatible trivializations and possible scalar factors
still have to be justified.

Still missing are the geometric lifting, the restriction/ideal bridge, the
line-bundle interpretation of the factorization, and the computation of global
sections. In particular, no theorem yet identifies the theta characteristic
with the hyperplane line bundle or proves its ineffectivity. Constructing a real
symmetric `5×5` linear determinantal representation is another missing theorem,
including its real descent hypotheses.

## 3. Identify the double cover and the Clifford class

Show that the cover obtained from the rank-four degeneration of the symmetric matrix agrees with the conic bundle's discriminant cover, with the correct real twist. A statement over the complex numbers alone does not settle the real twist.

`CofactorCover.lean` now also constructs a vector root from a nonzero square
pivot and explicit rank-one minor identities, and proves that the solution set
has exactly two elements when the characteristic is not two and a nonzero root
exists. It does not derive the minor identities from geometric corank,
construct a cover of schemes, prove étaleness, or associate a line bundle or
theta characteristic to it.

The root equation now has an explicit twist parameter. In particular, the
negative-adjugate equation must not automatically be used for the rank-four
degeneration of a five-dimensional form: the proposed signed-discriminant
convention differs from the rank-two degeneration of a three-dimensional
conic form. Identification of the correct geometric cover and twist remains
an obligation, even though the algebraic root lemmas support either sign.

The proposed argument also needs Brauer residues, an unramified/constant-class comparison, a real evaluation fixing the constant class, and a proof that the relevant even Clifford class has index at most two. These are absent from this project.

## 4. Prove isotropy of the five-dimensional form

The proposed route must justify:

1. Indefiniteness at every ordering of `ℝ(x,y)`, including the passage from real specializations to arbitrary orderings.
2. The exact quadratic-form classification turning anisotropy plus the Clifford index bound into a Pfister-neighbor situation; any scaling and discriminant conventions must be checked.
3. The signature and torsion argument in the Witt ring, and the needed result on the third power of its fundamental ideal for this field.
4. The resulting split eight-dimensional form and an actual isometric embedding of the five-dimensional form into it.

`IsotropicDimension.lean` proves only the final dimension argument. It also constructs the concrete split form `q(x,y)=Σ xᵢyᵢ` and proves that every five-dimensional subspace of its eight-dimensional space has isotropic restriction. It does not derive a split form from the geometry.

## 5. From generic isotropy to a real point of the net's base locus

The intended argument uses a zero-cycle theorem for systems of quadrics and a real-point consequence. Precisely state the theorem, check its field and dimension hypotheses, construct the zero-cycle of odd degree, and prove the required real closed field implication. Generic isotropy is not, by itself, a Lean proof that the intersection of three quadrics has a real point.

This bridge is not formalized. Names such as Amer–Brumer or Colliot-Thélène–Levine in an informal discussion do not supply a formal theorem or verify that the precise version required applies.

## 6. Incidence correspondence and rationality

Starting from a real base point, construct the hyperbolic reduction and identify the resulting equations with the intended conic bundle, including the relevant Clifford-class comparison. Prove a suitable minor is nonzero on a nonempty dense open set. Upgrade the cross-product formulas to inverse regular morphisms of scheme charts.

`Incidence.lean` gives explicit solutions of two linear equations and an equivalence of sets on a minor chart. The minor chart could be empty for a given parameter family. No density, regularity, birational map, or rationality theorem is proved.

## 7. Real rationality and connectedness

Precisely state and prove the necessary invariance/connectedness result for smooth projective real varieties, including nonemptiness. Apply it to the actual total space.

`ConnectedComponents.lean` only proves the elementary consequence of an explicit `ConnectedSpace` assumption using the genuine connected-component quotient. It does not establish that assumption for any conic bundle.

## Acceptance criterion for the full theorem

A completed proof would have an actual geometric statement, explicit original hypotheses, and a Lean proof depending only on accepted foundational axioms and proved mathematics. It would neither take rationality/connectedness as an extra unexplained premise nor encode the desired conclusion inside a definition of the hypotheses. The current repository does not meet this full-theorem criterion and does not claim to.
