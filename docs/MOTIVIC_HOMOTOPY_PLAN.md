# Motivic homotopy development plan

The first endpoint is natural Nisnevich representability for the motivic cohomology groups
already defined by Colib. Use `PresheafWithTransfers.motivicSheafComplex` and
`PresheafWithTransfers.motivicFiniteSheafComplex` as the coefficient complexes. The second
is the multiplication cone on the ordinary underlying integral complex. Preserve its integral
reduction and positive connecting map in comparisons. COL-1008 and COL-1007 give the
weight-one norm and graph formulas for checking the represented degree-one classes.
[Motivic Cohomology](library/chapters/motivic-cohomology.toml)

## Nisnevich representability

1. For a pointed simplicial presheaf apply objectwise reduced free abelianization, degreewise
   Nisnevich sheafification, and then normalized Moore chains. On the underlying pointed
   presheaf use Mathlib's simplicial circle to identify smash suspension with the actual
   reduced cone quotient. Record the cone map in the comparison.
2. Use the actual pointed Nisnevich neighborhoods of points of smooth schemes. Prove that
   these points are jointly conservative, and compare reduced normalized chains after taking
   each site fiber. An equivalence on the realizations of the stalk simplicial sets then
   induces a quasi-isomorphism of reduced sheaf chains. This makes their derived functor
   available on the localization of pointed simplicial presheaves.
3. For a cochain complex \(A\), shift its functorial K-injective resolution by \(p\).
   Apply inverse Dold–Kan to the resulting connective chain truncation.
   The zero point comes from the additive
   structure. Compare maps from a localized pointed presheaf to this object with derived
   maps from its reduced chains. On a representable \(X_+\), the reduced chain complex
   identifies with the free representing Nisnevich sheaf in degree zero. This gives natural
   bijections for both \(H^{p,q}(X,\mathbb Z)\) and \(H^{p,q}(X,\mathbb Z/n)\) using the
   existing complexes and pullbacks.
4. Extend the comparison to coefficient maps, including the integral reduction and the
   connecting morphism at the actual cone sign. Check the suspension degree shift and the
   resulting Bockstein on the represented classes. COL-1018 identifies the positive
   mod-\(n\) Bockstein as the connecting map of the actual
   \(K/n\to K/n^2\to K/n\) triangle and proves its square-zero formula on cochains.
   COL-1019 gives the action of the same map on reduced motivic cohomology.

The construction uses the Nisnevich localization and the specified K-injective resolutions.
The smooth-site specialization imports the existing motivic coefficient complexes. Keep the
generic point, chain, realization, and derived-category lemmas at their mathematical owners.
The Motivic Homotopy chapter contains the pointed constructions used for motivic homotopy
and the smooth-site representability results.
[Morel–Voevodsky, \(\mathbb A^1\)-homotopy theory of schemes](https://www.math.ias.edu/vladimir/node/65)
· [Voevodsky and Deligne, Lectures on motivic cohomology 2000/2001](https://arxiv.org/abs/0805.4436)

## Adapting the earlier Colib development

The earlier development at `6897d796398e` is the proof source for the pointed
presheaf, Nisnevich, affine-line, Čech, and Tate constructions. Its revert is
`6bd21f3`. Reuse the current reduced torus, transfer singular complex, ordinary
motivic complexes, and multiplication cone. Adapt the reduced Bockstein to the
positive connecting morphism and current reduction maps. Use the current
`SmoothSite.Contraction` projections and the native torus identity for the strict
Tate quotient. Recover the original collapse maps, distinguished-square
comparison, and Čech generators in that order. Match current Library identifiers
to the adapted mathematical endpoints.
[Earlier development](https://github.com/kangxyz/colib/commit/6897d796398ea31071d8dd84217b87fe68df54a8)
· [Revert](https://github.com/kangxyz/colib/commit/6bd21f3)

## A¹-localization and the Tate suspension

1. In the Nisnevich homotopy category, localize at the actual pointed projections
   \((X\times\mathbb A^1)_+\to X_+\). The comparison in COL-1016 assumes invariance of
   reduced hypercohomology under every pointed cylinder projection. Identify the scheme
   projections with the cylinders on representables and prove the extension from the
   geometric tests to the required cylinders. To identify the entire mapping spaces, use
   the invariance in all degrees that occur as their homotopy groups. The strict
   \(\mathbb A^1\)-invariance migration supplies the corresponding sheaf-cohomology theorem.
   The comparison for the actual coefficient complexes also needs a truncation or finite
   Nisnevich cohomological dimension argument for passage from cohomology sheaves to
   hypercohomology.
2. Develop the pointed constructions for \((\mathbb G_m,1)\) and
   \((\mathbb P^1,\infty)\), with their actual maps. Compare the motivic Tate sphere with
   \(S^1\wedge(\mathbb G_m,1)\), and record the comparison on reduced chains. The geometric
   cofiber constructions and explicit maps in COL-1017 and the stalkwise quotient
   comparison in COL-1020 give the map from the Tate cone to the quotient.
   COL-1036 uses the connecting morphism of the reduced cochain sequence of
   the Laurent-open quotient to send the forward coordinate to bidegree \((2,1)\).
   Tate smash preserves stalkwise weak equivalences by COL-1035. It also sends the
   pointed \(\mathbb A^1\)-cylinder projection to an \(\mathbb A^1\)-weak equivalence
   by the isomorphism that interchanges smash and cylinder.
   Construct the stalkwise right adjoint from the pointed internal Hom and
   Nisnevich fibrant replacement. Tate smash preserves stalkwise trivial
   monomorphisms, so its presheaf right adjoint preserves injective fibrancy.
   Identify injective fibrant replacement with the existing stalkwise
   localization. The resulting adjunction makes the right adjoint
   preserve \(\mathbb A^1\)-local targets, proving descent of Tate smash to the
   chosen localization. [Jardine, Motivic symmetric spectra, §§1.1–1.3](https://doi.org/10.4171/dm/86)
3. Use the product with the Tate class to construct the bonding maps
   \(K(\Lambda(q),2q)\wedge T\to K(\Lambda(q+1),2q+2)\). Verify the actual exterior-product
   maps, base points, signs, and coefficient functoriality. The normalized parameter
   product of COL-1037 supplies the signed integral cochain map. Extend it along
   the actual finite coefficient cone and compare it with the product on the
   pointed representatives. Identify the simplicial
   suspension with cup product by the simplicial suspension class and the Tate suspension
   with cup product by the Tate class. For the stable representation, prove the loop
   comparison in the chosen motivic model and identify its represented cohomology.
   Voevodsky's cancellation theorem supplies the effective-motive comparison for tensoring
   with the Tate motive. Relate it to the bonding maps used here.
   [Voevodsky, Cancellation theorem](https://ems.press/books/dms/255/5073)

For the cohomological suspension comparison, Voevodsky's Theorem 2.4
reduces to smooth representables and uses open excision for the quotient
of \(U\times\mathbb P^1\) by \(U\times(\mathbb P^1-\{0\})\).
The comparison with higher Chow groups takes
multiplication by the pulled-back Tate class to proper pushforward along
the point section. The higher Chow localization sequence gives the
isomorphism onto the kernel of restriction. A rank-two projective bundle
formula with the same first Chern class gives another route to that kernel.
The orientation comparison in Lemma 4.2 identifies the pullback of
Voevodsky's Tate class with \(c_1(\mathcal O(1))\) on \(\mathbb P^1\).
For the effective-motive comparison, use the explicit cancellation maps
on finite correspondences and their Suslin complexes.
[Voevodsky, Reduced power operations, §2, Theorem 2.4 and Lemma 2.5, and §4, Lemma 4.2](https://numdam.org/item/10.1007/s10240-003-0009-z.pdf)

## Tate cancellation on finite correspondences

The first theorem is the integral Suslin quasi-isomorphism of Voevodsky's
Corollary 4.9 for the existing smooth site and signed finite correspondences.
Use the relative Cartier intersection of §3 and the power cuts of §4.
For the effective-motive consequence start over a perfect field and target
\(DM^{\mathrm{eff}}_-(k)\) as in Corollary 4.10. The higher Chow comparison
belongs to the separate projective-line proof above.
[Voevodsky, Cancellation theorem, §§3–4](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published%20versions/cancellation_published.pdf)

### The actual comparison and its signed representatives

Use Cor.parameterProduct for the multiplicative group. In the chosen
right-factor coordinates, let \(e_X\) be the graph of projection followed
by the unit section on \(X\times\mathbb G_m\). Use the actual target
quotient of the representing transfer presheaf by the unit section.
Apply the existing contractionKernel to this quotient in the source
variable. The comparison into this presheaf is induced by exterior product
on the actual signed correspondences.

For each \(X,Y\), identify the sections of the comparison target with
the image of the two complementary idempotents on
\(\operatorname{Cor}(X\times\mathbb G_m,Y\times\mathbb G_m)\). Check that
the inclusion takes the comparison to
\(\operatorname{id}_{\mathbb G_m}\boxtimes W-e\boxtimes W\), in the
chosen product order. The comparison must be natural in the representing
target so it restricts to the image of the commuting unit-axis projectors
of a reduced transfer torus. The chain map uses singularComplexMap and
its literal face maps. [Voevodsky, Theorem 4.6 and Corollary 4.9](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published%20versions/cancellation_published.pdf#page=12)

### The power cuts and the parameter family

On a prime support \(P\) of a signed correspondence from
\(X\times\mathbb G_m\) to \(Y\times\mathbb G_m\), pull the two native
torus coordinates back to \(P\). Form the actual zero schemes of
\(t_1^{n+1}-1\) and \(t_1^{n+1}-t_2\). Prove finite support over \(X\)
for all sufficiently large \(n\), and show that the generic images of
the zero schemes give the required finite relative cycles. The signed
pushforward to \(X\times Y\) must compute \(\rho_n\) with the numerator
cycle positive. Extend this construction by the integer weights of the
actual finite support. Use a common exponent for every finite family of
cycles and pullbacks needed in an equality.

On affine charts, start with
LaurentPolynomial.exists_moduleFinite_quotient_span_T_sub_unit.
Integrality of \(t_2\) and \(t_2^{-1}\) gives monic relations for both
directions of the Laurent coordinate on the cut. For Remark 4.2 set
\(p=m+1,\ q=n+1,\ t=t_1,\ u=t_2\). Clearing the two denominators in
\(s g_m+(1-s)g_n\) gives \(A(t)-B(t)u\), with
\[
A=t^{p+q}-(1-s)t^p-s t^q,\qquad B=s t^p+(1-s)t^q-1 .
\]
The degree gap \(\min(p,q)\) absorbs the bounded Laurent coefficients
in the homogeneous monic equation. The reciprocal identities
\(t^{-p-q}A(t)=-B(t^{-1})\) and \(t^{-p-q}B(t)=-A(t^{-1})\)
give the other integrality bound using \(u^{-1}\). Check this over the
whole parameter ring and glue the finite cut schemes over the original
base. The endpoint computation must preserve the signed difference
when a factor common to numerator and denominator is cancelled.
[Voevodsky, Lemma 4.1 and Remark 4.2](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published%20versions/cancellation_published.pdf#page=10)

### Cycle coefficients and compatibility with correspondences

Use the zero-scheme cycles of CartierCycle and PrincipalSection and
the actual native finite pushforward. The initial signed-cut constructor
takes a finite-support witness for each cut and proves target graph
compatibility. Verify the generic-image witnesses from the geometry of
prime supports. Retain the two torus coordinates on the closed cut
support during the source-fibre calculation and project to \(X\times Y\)
after the cycle identity.

The first test of Proposition 3.1 is a non-flat closed simplex face on
one principal cut. For a flat integral relative curve on a DVR test
scheme, write \(B\) for the stalk at a closed-fibre cut point,
\(\pi\) for the base uniformizer, \(A=B/\pi\), and \(f\) for the
cut equation. When \(f\) is regular on the reduced fibre components
and its cut has finite length there, use \(M=B/(f)\) and
\(M_{\mathrm{tf}}=M/M[\pi^\infty]\). The fibre coefficient comparison
has the local form
\[
\ell(M_{\mathrm{tf}}/\pi)
=\ell(A/(f_s))-\ell(A[f_s])
=\sum_{\mathfrak p\in\operatorname{Min}A}
 \ell(A_{\mathfrak p})\ell((A/\mathfrak p)/(f_s)).
\]
For the first equality use flatness of the torsion-free quotient,
additivity of length, and the relation \(fx=\pi y\) identifying
the relevant torsion kernels. For the second use the weighted principal
Euler associativity of COL-0173. Match the resulting coefficients with
the actual cycle of the Cartier cut and the native fibre cycle.

Use StacksFrontier's DVR weighting and specialization of coherent
modules to pass from this stalk comparison to the relative cycle
specialization. Audit the integral-closure generators and the
comparison with the chosen incidence Tor composition on signed Cor.
The endpoint is the literal multiplicity identity under relative
pullback in the admissible case, its projection formula, and hence
Lemma 4.4 for precomposition by finite correspondences. Use the
target-graph case of Lemma 4.5 for external parameters. The available
relative Gysin identity in StacksFrontier is expressed modulo rational
equivalence. The Suslin face computation uses the cycle coefficients.
[Voevodsky, Proposition 3.1, Lemma 3.2 and Lemmas 4.4–4.5](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published%20versions/cancellation_published.pdf#page=5)

### Large-exponent compatibility via a new torus parameter

For the large exponents used in Corollary 4.9, establish Lemma 4.4
by retaining both original coordinates and inserting a third torus
parameter. With \(N=n+1\) and original units \(t,v\), the two parameters
are \(\lambda=t^N\) and \(\lambda=t^N/v\). For each parameter, push the
support along its closed graph into
\((X\times\mathbb G_{m,\lambda})\times
(\mathbb G_{m,t}\times Y\times\mathbb G_{m,v})\).
Over \(X\times\mathbb G_{m,\lambda}\), the finite zero schemes of
\(t^N-\lambda\) and \(t^N-\lambda v\) identify with these graph supports.
Use the affine Laurent bounds and quasi-compact gluing. Verify that
the new finite support dominates the same component over \(X\).
Taking the fibre at \(\lambda=1\) recovers each original zero scheme
with its scheme structure.

For a prime precomposition with support \(Q\subset X'\times X\) and
an original support \(P\), identify the two incidence schemes with
\(Q\times_X P\). At a point of this incidence, let \(C\) be an affine
coordinate ring of \(Q\times_k P\). In the two support-product charts
the first diagonal equation is \(u-\ell\) on \(C[u,u^{-1}]\), where
\(\ell=t\) in the original chart and \(\ell=\lambda(t,v)\) in the
new chart. Both regular equations identify the localized quotient
with the same stalk of \(Q\times_k P\) by evaluation. The remaining
equations come from one local diagonal list for \(X\), pulled back
by the same maps from \(Q\) and \(P\). Use the regular leading block
of the existing incidence Koszul comparison. Check the equality of
each Tor length on the common quotient stalk and retain the same
outer pushforward and residue degrees. Extend the resulting cycle
equality by the original integer coefficients.

Precompose the retained cycle with the graph of \(\lambda=1\).
Use the Cartesian endpoint formula with the open immersion of the
torus in the affine line and commute the unit graph with the
original exterior correspondence. Project to \(Y\) and take the
difference of the two cuts. The acceptance condition is the
equality on native finite correspondences for a common large
exponent, including every simplex face in the given finite family.
[Voevodsky, Lemmas 4.1 and 4.4](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published%20versions/cancellation_published.pdf#page=10)

### Graph normalization and interchange of two torus factors

On the diagonal torus support the two cuts have the actual ranks
\(n+1\) and \(n\), using \(t_1^{n+1}-t_1=t_1(t_1^n-1)\).
The cut at the constant unit has equal numerator and denominator cycles.
Use nativeExterior_single to prove the identity on each generator of an
arbitrary exterior correspondence. Identify the literal zero schemes
with the base changes of the monic Laurent quotients and use their
finite-flat pushforward ranks, including inseparable multiplicities.
This gives the left inverse on \((1-e)\boxtimes W\).

Independently, for units \(a,b\) on the universal torus use the monic
quadratic family between \((z-ab)(z-1)\) and \((z-a)(z-b)\).
Its constant coefficient is \(ab\). Use the existing graph-restriction
and polynomial-cycle product formulas to compute the two endpoint
cycles. Push the family to the diagonal torus to establish diagonal
additivity, and to the paired torus with one coordinate fixed to
establish bilinearity. Polarize to obtain the signed interchange
relation after the two unit projections. Convert the relation on
the universal torus to the actual \(\mathbb A^1\)-homotopy between
interchange and inversion on the reduced factors.
[Voevodsky, Lemmas 4.3, 4.7 and 4.8](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published%20versions/cancellation_published.pdf#page=10)

### Suslin homology and the effective-motive comparison

Use Mathlib's homotopy equivalence between the normalized Moore
complex and the alternating face map complex of the actual evaluated
simplicial transfer group. Its normalization kills the positive
faces, and its cycles also kill the zeroth face. Identify those
cycles with transfer maps from the representable of
\(X\times\Delta^r\) quotiented by all actual faces. A normalized
boundary is the zeroth face of a chain with all other faces zero.
The map to the next simplex with barycentric coordinates
\((s,(1-s)t_0,\ldots,(1-s)t_r)\) gives the corresponding relative
\(\mathbb A^1\)-homotopy to zero. In the other direction, sum the
actual prism restrictions of a relative homotopy. The face terms
along the boundary vanish and the remaining differential is the
difference of the endpoints.

Use the face-compatible \(\rho_n\) on the finite family of chains,
faces and homotopies, and use the interchange homotopy to prove
the two inverse identities on homology as in Theorem 4.6 and
Corollary 4.9. The quasi-isomorphism must be the one induced by
torusCancellationChainMap on the current native complexes.

### Derived contraction and effective motives

Use Mathlib's bounded-above DerivedCategory.Minus of Nisnevich
sheaves with transfers, and take the full subcategory cut out by
\(\mathbb A^1\)-invariance of all cohomology sheaves. Put the
existing singular chain complex into cochain degrees \(-r\) and apply
the existing exact transfer sheafification. This is the representative
motive of a smooth scheme when applied to its actual transfer
representable. Prove the localization property of this construction
on bounded-above complexes by the augmentation and the native
geometric interval homotopy. Use finite sums in each degree of the
bounded-above total complex.

The torus projection on the underlying Nisnevich site gives the
right-derived reindexing functor. Start at the original section functors
and split off the base summand by projection and unit. For positive
degrees use strict \(\mathbb A^1\)-invariance of the cohomology presheaf
with transfers and the existing torus affine-localization zero theorem.
Its generic-open zeros give zero after sheafification on the actual
small Nisnevich site. Use transferExtEquiv and its graph and coefficient
naturality to identify this with the higher derived reindexing of an
injective resolution. For the corresponding small-site direct image,
identify the base-change diagram of the torus projection and apply the
existing derived point-fibre colimit comparison.

For degree zero compare sheafification and torus reindexing on an
\(\mathbb A^1\)-invariant presheaf with transfers. The kernel and cokernel
of the sheafification unit have locally zero sections. Lift the local
zero condition on the integral Laurent chart to a generic open
restriction and use the existing base-shrink theorem to descend
the vanishing to the original base. Exact reindexing and sheafification
then identify the actual sheafification of the torus sections with
the torus sections of the sheafification. Apply this comparison to
the homology of the raw singular complex. The existing parameter
permutation identifies the torus and simplex factors degreewise.
Use derived truncations or the corresponding Leray spectral sequence
to pass from the two cohomology statements to the bounded-above
complexes of equation (4.3).
[Voevodsky, Cancellation theorem, Corollary 4.10 and equation (4.3)](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published%20versions/cancellation_published.pdf#page=14)
· [Voevodsky, Cohomological theory of presheaves with transfers, Proposition 4.34](https://www.math.ias.edu/Voevodsky/files/files-original/Dropbox/Published_papers/Motives/Collection/s3.pdf#page=41)

For the left adjoint, extend the actual additive torus product
functor \(F\) from transfer representables. On a presheaf \(P\) and
source \(X\), use the sum of
\(\operatorname{Cor}(X,FY)\otimes_{\mathbb Z}P(Y)\) over \(Y\) and impose
the relations for the actual maps of the correspondence category.
The adjunction with reindexing has unit represented by
\(\operatorname{id}_{FY}\otimes p\), and counit given by transfer on
the first factor. Check these formulas on the original representable
generators. Sums of the large transfer representables give projective
presentations before sheafification. Derive the extension using these
presentations and verify descent through the actual Nisnevich and
effective localizations. Check descent on the generating Nisnevich
relations and the literal product of the affine-line projections.
The complementary unit projector gives tensoring with the reduced
transfer torus. Identify the resulting adjunction with
the one computed by derived contraction and identify its unit on
representables with the map of Corollary 4.9. Prove the
representable-generator reduction using bounded-above resolutions,
with the required coproduct and truncation compatibilities. This
gives full faithfulness for the reduced transfer torus. Use the
weight-one comparison to identify the shift of this functor with
the actual Tate twist. Compare the resulting map on each motivic
weight and finite coefficient cone with the existing signed Tate
bonding maps. The derived Tate loop adjunction on motivic spaces
supplies the corresponding space-side comparison.

Bachmann's Proposition 2.16 gives a separate categorical packaging
of the retraction and interchange steps. Bachmann–Elmanto §4F gives
additional detail for uniform parameter support. Use their relevant
lemmas to check the finite-correspondence argument above.
[Bachmann, Proposition 2.16](https://arxiv.org/pdf/2006.14934)
· [Bachmann–Elmanto, §4F](https://msp.org/obs/2025/6-1/obs-v6-n1-p01-p.pdf)

### Implementation milestones

The geometry, graph calculations, cycle-coefficient comparison, and
transfer-complex interfaces have disjoint owners. Finish the current
comparison map, graph-rank computation, affine finiteness, and signed
cut with their exact hypotheses first. Check the non-flat coefficient
identity as the next proof milestone while the parameter family and
interchange homotopy proceed in parallel. Assemble the signed
correspondence identities before recording Corollary 4.9 as proved.
Treat the derived comparison and Corollary 4.10 as subsequent milestones.

Keep the cut calculations under Correspondences, the affine finiteness
under Polynomial, and the comparison and Suslin theorem under
PresheavesWithTransfers. The first chain comparison belongs in the
transfer singular-complexes section. Register the actual mathematical
items and their precise source locators at a checked milestone.
Run changed leaves with the pinned Lean, Mathlib and Stacks artifacts
through one remote queue. Record source hashes and reuse compatible
compiled dependencies for the native final checks.

## Reduced powers and the norm-residue proof

Construct the total power on the unstable representatives, keeping the diagonal and the
finite-group action visible in the comparison with transfer complexes. Work at a prime
invertible in the base for the norm-residue application. Use Riou's relative smooth site
construction for well-definedness of the total power and his proof of Bockstein
vanishing for the symmetric-group power. Identify the operation's
coefficients and prove naturality, suspension compatibility, and the Cartan and Adem
relations used to form the Milnor operations. The proof of the mod-two case also needs
their action on Thom classes and the Margolis vanishing for reduced Čech cones. The
general-prime argument uses the comparison of its symmetric-power construction with
\(\beta P^n\) up to a nonzero scalar, with the hypotheses of Voevodsky's Theorem 3.8.
[Reduced power operations](https://arxiv.org/abs/math/0107109)
· [Riou, Opérations de Steenrod motiviques, §§3.6–3.7](https://arxiv.org/abs/1207.3121)
· [On 2-torsion in motivic cohomology](https://arxiv.org/abs/math/0107110)
· [On motivic cohomology with \(\mathbb Z/\ell\) coefficients](https://arxiv.org/abs/0805.4430)

## Comparison with later constructions

Voevodsky computes motives of unstable representatives and studies operations using derived
symmetric powers. This is the source for the unstable comparison needed in the general
norm-residue argument. Hoyois–Kelly–Østvær compute bistable operations and spectrum
cooperations in positive characteristic at primes invertible on the base. Their results
provide a later comparison for the stable model and specify what the spectrum should
recover. [Voevodsky, Motivic Eilenberg–MacLane spaces](https://pmihes.centre-mersenne.org/articles/10.1007/s10240-010-0024-9/)
· [Hoyois–Kelly–Østvær, The motivic Steenrod algebra in positive characteristic](https://arxiv.org/abs/1305.5690)

Framed recognition gives a different presentation of motivic infinite \(\mathbb P^1\)-loop
spaces. Comparing it with the present finite-correspondence and chain-complex construction
would need framed transfers and their compatibility with the existing finite
correspondences. Bachmann and Hopkins' November 2026 preprint addresses the
characteristic-prime case via a homotopical model for the Eilenberg–Mac Lane spaces, with
normed structures and \(\mathbb P^1\)-loop-space calculations as inputs. Treat its
characteristic-prime computations as a separate comparison target.
[Elmanto–Hoyois–Khan–Sosnilo–Yakerson, Motivic infinite loop spaces](https://arxiv.org/abs/1711.05248)
· [Bachmann–Hopkins, Motivic Eilenberg–Mac Lane spaces at the characteristic](https://arxiv.org/abs/2611.02320)
