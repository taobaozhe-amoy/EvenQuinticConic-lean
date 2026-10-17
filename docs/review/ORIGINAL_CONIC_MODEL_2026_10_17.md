# Audit of the original conic-bundle input and its quadratic model

Date: 2026-10-17. Scope: the **first geometric bridge only**. This is a mathematical review, not a new Lean theorem or a certification of the final real-connectedness claim.

## Conclusion

Under the usual meaning of a smooth projective, geometrically standard real conic bundle, the original morphism does admit a global line-bundle-valued quadratic presentation of rank three. No additional arithmetic splitting assumption and no real rational point are needed for this presentation. A smooth discriminant gives rank exactly two along the geometric discriminant. The total space is geometrically integral.

There are three important qualifications:

1. Prokhorov's stated ground-field convention does not directly include the real field. One must either supply descent or cite a source that treats nonclosed fields.
2. Relative Picard number one **by itself** does not imply relative anticanonical ampleness. In the standard definition ampleness is already included; alternatively it follows using the smooth-conic generic fibre and the projectivity hypotheses, as explained below.
3. The term conic bundle must retain its usual generic-conic/connected-contraction content. Flatness, relative dimension one, and anticanonical positivity alone do not exclude a finite nontrivial Stein factor. A formal definition cannot silently discard this content.
4. This rank-three quadratic bundle is not yet the later symmetric **five-by-five linear matrix net**. The even-theta representation, descent, and comparison with the actual conic bundle are separate obligations.

## What the cited definitions actually say

[Prokhorov, arXiv:1712.05564v6](https://arxiv.org/pdf/1712.05564), §2, works over an algebraically closed field of characteristic zero unless specified otherwise. Definition 3.1 requires a proper flat morphism between smooth varieties, relative dimension one, and relatively ample anticanonical bundle; “standard” adds equivalent minimality conditions, including relative Picard number one. Theorem 3.2 uses \(E=\pi_*\omega_X^{-1}\), of rank three, embeds X into the quotient-convention \(\mathbb P_S(E)\), and places its defining section in

\[
H^0\!\left(\mathbb P_S(E),\,\mathcal O(2)\otimes p^*(\det E^\vee\otimes\omega_S^{-1})\right).
\]

Section 3.3 identifies the discriminant by the local determinant and identifies double-line fibres with singular discriminant points. These statements must not be cited as literally stated over the real field.

A direct nonclosed-field source is [Frei–Ji–Sankar–Viray–Vogt, *Curve classes on conic bundle threefolds and applications to rationality*, Algebraic Geometry 11 (2024), 421–459](https://api.algebraicgeometry.nl/Article/20462/2024-3-014.pdf), §2, printed pp. 425–427, especially p. 426. It works in characteristic different from two, states the same global rank-three quadratic presentation, and explains geometric standardness and geometric ordinariness. Thus it applies to the real field. Smooth discriminant fibres have rank at least two there. Its introductory warning is also relevant: over nonclosed fields the discriminant cover does not in general determine the generic conic. That later arithmetic comparison cannot be inferred merely from this model theorem.

## When Picard rank one does supply ampleness

Here is the required argument, rather than the unsupported implication “rho equals one, hence ample.” Work first after extension to the complex numbers. Suppose the morphism is projective, the total space is smooth, its general fibre is a smooth conic, and its relative numerical Picard number is one. Choose a relatively ample divisor H. The relative numerical class of minus the canonical divisor is a scalar multiple a[H]. On a smooth general fibre C, the anticanonical degree is two, whereas H has positive degree. Consequently a is positive. The relative Kleiman criterion now proves relative ampleness. Descent of relative ampleness returns the result over the real field.

The criterion is stated in [Fujino, *Foundation of the minimal model program*, author manuscript, Theorem 2.2.3](https://www.math.kyoto-u.ac.jp/~fujino/foundation1.pdf), and in Kollár–Mori, *Birational Geometry of Algebraic Varieties*, Theorem 1.44 ([publisher record](https://doi.org/10.1017/CBO9780511662560)). Descent is [Stacks, §35.25, Lemma 35.25.1](https://stacks.math.columbia.edu/tag/02LB).

The fibre hypothesis is essential to this argument: an elliptic curve times the projective plane has relative numerical Picard number one over the plane, but its anticanonical restriction to the fibre has degree zero.

Conversely, flatness and relative anticanonical ampleness alone do not force a geometrically connected generic fibre: composing a projective-line bundle with a nontrivial finite flat cover of the base illustrates the missing Stein-factor condition. The conventional conic-bundle generic fibre, or the connected-contraction requirement, must be kept explicit when unpacking the literature.

If “conic bundle” means only a morphism whose generic fibre is a conic, flatness is not part of that terminology. In the smooth-threefold Mori-contraction setting it can be recovered by an additional theorem, but this theorem must actually be invoked. For the present task, retaining the ordinary conic-bundle definition is the cleanest precise input.

## A canonical real construction, with descent made explicit

The following is a reconstruction of the bridge from standard descent facts. It avoids choosing a complex equation and assuming its coefficients can be made real.

Let S be the real projective plane and let pi: X → S satisfy the conic-bundle hypotheses. Define

\[
H=\omega_X^{-1}\otimes\pi^*\omega_S,
\qquad A=\pi_*H.
\]

Since X and S are smooth over the real field, their canonical line bundles commute with extension to the complex field. Thus H also commutes with that extension. The use of H instead of the absolute anticanonical bundle is only a twist pulled back from S.

### 1. The rank-three bundle is already defined over the real field

The canonical flat-base-change map identifies

\[
A_{\mathbb C}\simeq\pi_{\mathbb C*}H_{\mathbb C}.
\]

The right-hand side is locally free of rank three by the geometric conic model theorem. The left-hand side is the base change of the actually defined real sheaf A. Finite local freeness descends, and the rank is preserved by extension of residue fields; hence A is a real vector bundle of rank three.

Precise tools: [Stacks, Lemma 30.5.2, tag 02KH](https://stacks.math.columbia.edu/tag/02KH), for flat base change of higher direct images of quasi-coherent sheaves under a quasi-compact, quasi-separated morphism; [Stacks, Lemma 35.7.6, tag 05B2](https://stacks.math.columbia.edu/tag/05B2), for descent of finite local freeness. Properness supplies the finiteness conditions here. Flatness of the **base change** is what is used in tag 02KH; this is different from a fibrewise cohomology-and-base-change assertion.

### 2. The anticanonical embedding descends canonically

The evaluation morphism

\[
\pi^*A\longrightarrow H
\]

is surjective after extension to the complex field, hence is surjective before extension by faithful flatness. Adopt the convention that \(\mathbb P_S(A)=\operatorname{Proj}_S\operatorname{Sym}A\) parametrizes one-dimensional quotients of A. Evaluation constructs an actual real morphism

\[
i:X\longrightarrow\mathbb P_S(A),\qquad i^*\mathcal O(1)\simeq H.
\]

Its complexification is the anticanonical closed immersion. Therefore i is a closed immersion by [Stacks, Lemma 35.23.21, tag 02L6](https://stacks.math.columbia.edu/tag/02L6). This is descent of a property of an already constructed real morphism, not an appeal to effective descent of an unspecified projective variety.

### 3. The ideal and the quadratic equation descend without a choice of generator

Write p: P = P_S(A) → S and let J be the ideal sheaf of i(X). Since complexification is flat, J pulls back to the actual complex ideal. Set

\[
W=p_*(J\otimes\mathcal O_P(2)).
\]

After complexification, the quadratic presentation says that \(J_{\mathbb C}(2)\) is pulled back from a line bundle on \(S_{\mathbb C}\). Since \(p_{\mathbb C*}\mathcal O_{P_{\mathbb C}}=\mathcal O_{S_{\mathbb C}}\), flat base change identifies \(W_{\mathbb C}\) with that line bundle. Hence W is invertible. The canonical evaluation

\[
p^*W\longrightarrow J(2)
\]

becomes an isomorphism after complexification; its kernel and cokernel therefore vanish by faithful flatness. Consequently

\[
J\simeq\mathcal O_P(-2)\otimes p^*W.
\]

Put \(V=A^\vee\) and \(L=W^\vee\). The inclusion of this ideal is equivalently a global section

\[
q\in\Gamma\bigl(S,\operatorname{Sym}^2 V^\vee\otimes L\bigr),
\qquad X=V(q)\subset\mathbb P_S(V)
\]

where the last projective-bundle notation uses the **lines-in-V** convention. No global trivialization of V or L is asserted. Since two is invertible, q also defines an L-valued symmetric bilinear pairing and a symmetric bundle map \(V\to V^\vee\otimes L\).

An equivalent construction defines W as the kernel of
\(\operatorname{Sym}^2 A\to\pi_*H^2\). To use this version, one must establish local freeness and base change of the second pushforward and surjectivity of multiplication; these are not consequences of notation alone. The ideal construction above avoids that extra detour.

The projective-bundle identifications and the quotient convention are recorded in [Stacks, §27.21, tag 01OA](https://stacks.math.columbia.edu/tag/01OA). The ideal is a relative effective Cartier divisor because X is flat over S; compare [Stacks, §31.19, tag 056P](https://stacks.math.columbia.edu/tag/056P). These arguments use the existing real sheaf J throughout and do not select a complex generator requiring additional descent data.

## Discriminant, rank two, and the actual double cover

In local trivializations of V and L write q as a symmetric three-by-three matrix Q. The invariant determinant is a section of

\[
(\det V^\vee)^{\otimes2}\otimes L^{\otimes3}.
\]

The discriminant relevant here is its **effective divisor with scheme structure**, not merely the reduced support of a determinant polynomial. For a smooth conic bundle this agrees with the usual reduced discriminant divisor. The global model theorem and its degeneration statement justify this identification; it must be retained when translating the input to Lean.

Here is the elementary rank test once that identification is available. At a geometric discriminant point, rank at most one would make every two-by-two cofactor vanish. The differential of det Q is the sum of these cofactors times the differentials of the entries of Q, so it would vanish. This contradicts smoothness of the discriminant divisor inside the smooth base. Thus rank is exactly two on the discriminant and three outside it.

Keeping the scheme structure matters. For example, diag(1,t,t) has determinant t squared, whose reduced support is smooth, although the central quadratic form has rank one. It is not a counterexample to the original hypotheses: the resulting total family is singular at geometric points. It does show that “the reduced determinant support is smooth” alone is insufficient for the cofactor argument.

At rank two, the radical is a line and the induced binary quadratic form is nondegenerate. Its two geometric isotropic lines give the two components of the singular conic. Their finite étale parameter scheme is the discriminant cover of the **actual** bundle. Identifying its associated two-torsion line bundle with the theta characteristic used in a later representation theorem remains a separate comparison; it is not furnished by rank two alone.

## Geometric integrality of X

This can be proved without adding it as an independent hypothesis, provided the stated conic-bundle conditions hold. After extending to the complex field, the total space is smooth, hence regular, reduced, and normal. It is Noetherian, so its irreducible components are disjoint and open as well as closed; see [Stacks, §28.7, Lemmas 28.7.5–28.7.8, tag 033H](https://stacks.math.columbia.edu/tag/033H).

Each nonempty component maps to a closed subset of the base by properness and to an open subset by flatness and finite presentation ([Stacks, Lemma 29.26.10, tag 01UA](https://stacks.math.columbia.edu/tag/01UA)). Since the base is connected, each such component surjects. Two components would therefore disconnect the geometric generic fibre. But that fibre is a smooth plane conic, hence geometrically integral. There is exactly one component, and the total space over the complex field is integral. This is geometric integrality over the real field.

This argument concerns the scheme X after extending scalars. It says nothing about the number of connected components of the Euclidean space X(real numbers).

## Precise boundary for the proposed Lean input

The following input is sufficient for this first bridge:

- S is the real projective plane.
- X is a smooth projective real threefold and pi is a proper flat morphism of relative dimension one, with smooth geometrically integral conic generic fibre and relatively ample anticanonical bundle (or a proved equivalent standard conic-bundle definition).
- The actual discriminant divisor is smooth of degree five.
- Geometric standardness means the corresponding relative Picard number after extension to the algebraic closure is one.
- The specified double cover is the component cover of this actual morphism.

The smooth geometrically integral generic-conic condition in this list is part of the ordinary meaning of conic bundle, not a condition asserting that the generic conic has a rational point.

The rank-three model itself does not use the degree five condition or the evenness condition. Those enter subsequent steps. Under the standard definition this is an unpacking of the original hypotheses, not a stronger theorem. If a formal input retains only a generic conic, a Picard-rank numeral, or a reduced discriminant support, it has omitted part of the bridge and must either add the omitted hypotheses or prove the appropriate recovery theorem.

In particular, this review does **not** prove any of the following: existence of a split five-by-five real linear determinantal representation, existence of a common real point of its quadrics, equality of the real generic conic with the reconstructed generic conic, or connectedness of the real total space. A Brauer-class discrepancy between two real models with the same cover remains a substantive issue beyond the present scope.
