# Unstable motivic homotopy foundations

## Target and source basis

Construct the pointed unstable Nisnevich–A¹ homotopy theory and the reduced
motivic cohomology interfaces used in Riou's total powers and in the
norm-residue proof. The initial mathematical base is a field of characteristic
zero. Work relative to its smooth separated finite-type schemes when the
construction requires a base change. The coefficient prime is a parameter.

The source baseline is Colib `ebc8d39a2c04de660b7ccfb929bbb95a32f186b0`,
Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and Stacks
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7`. The independent Motivic migration
source is `a6805c4a87cdfd7717dd7a94039246a167f15380`.

| Input | Current supplier | Required new comparison |
| --- | --- | --- |
| Smooth site, products, Nisnevich squares | Colib `AlgebraicGeometry.Sites.Smooth` | Simplicial Nisnevich descent and comparison with the chosen localization |
| Spaces and weak equivalences | Mathlib `SSet` and Colib `SSet.IsRealizationWeakEquivalence` | Pointed presheaf model, local weak equivalences and the homotopical localization theorem |
| Finite correspondences and transfers | Colib `Correspondences.Category`, `PresheavesWithTransfers`, `SheavesWithTransfers.Sheafification` | Reduced transfer torus, singular complex with transfers and its multiplicative and derived interfaces |
| Ordinary cohomology | Colib `CategoryTheory.Sites.Hypercohomology` | Actual reduced chains on pointed simplicial presheaves and their comparison on representables |
| Simplicial algebra | Mathlib Čech nerves, extra degeneracies, Dold–Kan and model-category foundations | Motivic representability and compatibility of reduced chains with the two suspensions |
| Tate geometry | Colib `Scheme.PolynomialLaurent` and Stacks scheme geometry | The zero-complement identification, the actual Tate sphere comparison, and relative homotopy purity and Thom |

## Comparison with later constructions

| Route | Mathematical gain | Use in this formalization |
| --- | --- | --- |
| Brown–Gersten via a cd-structure | The pointed local class is generated under the appropriate closure by elementary squares and objectwise weak equivalences. Adding affine-line projections gives a presentation of unstable motivic homotopy. | Match the existing generators and prove the completeness, regularity and boundedness statements on the selected smooth site. The reverse inclusion uses the closure theorem and local replacement. Voevodsky, [Completely decomposable topologies, Theorem 3.11](https://arxiv.org/pdf/0805.4578#page=20) and [Unstable motivic homotopy categories, Propositions 3.1 and 3.7](https://arxiv.org/pdf/0805.4576#page=12). |
| Revised norm-residue argument | Voevodsky's final paper replaces the disputed earlier operation lemma using a modification of Weibel's argument. It also gives another proof at the prime two. Haesemeyer–Weibel fix the proportionality constant using a projective bundle and the cyclic classifying space with their normalization. | Use the corrected unstable recognition criterion as the common odd-prime endpoint. Record the exact coefficient and sign comparison before using the normalization. Voevodsky, [On motivic cohomology with Z/ℓ-coefficients, Introduction and Theorem 3.8](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/on_motivic_with_Zl_published.pdf), and Haesemeyer–Weibel, [The Norm Residue Theorem, Corollary 6.34 and Theorem 15.38](https://sites.math.rutgers.edu/~weibel/BK.pdf). |
| Riou's relative total power | The relative Thom class, functoriality in the finite étale torsor and independence of the bundle give the power map on the diagonal representing spaces. | Use the existing finite correspondences and prove the relative Thom and base-change statements on that model. Riou, [Opérations de Steenrod motiviques, §§1–2 and §3.7](https://arxiv.org/abs/1207.3121). |
| Stable and framed models | Spitzweck constructs a multiplicative motivic spectrum over arithmetic bases. Its finite-coefficient construction over those bases uses the norm-residue theorem. Framed recognition presents effective motivic spectra over perfect fields in terms of grouplike framed motivic spaces. | Use these as downstream comparison targets for a stable library. The arithmetic construction has a dependency on the theorem being formalized. Spitzweck, [A commutative P¹-spectrum, Corollary 7.19 and Theorem 8.22](https://arxiv.org/abs/1207.4078), and Elmanto–Hoyois–Khan–Sosnilo–Yakerson, [Motivic infinite loop spaces, Theorem 3.5.14](https://hoyois.app.uni-regensburg.de/papers/deloop.pdf). |
| Normed motivic spectra | Finite étale norms of motivic spectra recover the total power on homogeneous classes for the normed motivic cohomology spectrum. | Use this as a later coherence and comparison target, with the torsor power already specified on the unstable diagonal spaces. Bachmann–Hoyois, [Norms in motivic homotopy theory, Example 7.25 and Theorem 14.5](https://arxiv.org/abs/1711.03061). |
| Diagonal comparison without desingularization | Hu gives a finite-linear-quotient proof of the reduced free-transfer comparison for diagonal Eilenberg–Mac Lane spaces between the specified smooth and seminormal sites. | The candidate could remove the resolution input for the diagonal comparison. Check admissibility, the actual comparison map and the operation needed in odd degree before adoption. Hu, [Motivic Steenrod algebra and Thom obstructions without desingularization, v1, Theorems 4.8–4.9](https://arxiv.org/html/2609.14128v1#S4.SS4). |
| Positive characteristic and the coefficient characteristic | Hoyois–Kelly–Østvær classify bistable operations away from the characteristic. Bachmann–Hopkins give a new model for diagonal p-local Eilenberg–Mac Lane spaces in characteristic p using normed monoids. | Use the former for an extension away from the characteristic. The latter has stable and normed prerequisites. Hoyois–Kelly–Østvær, [The motivic Steenrod algebra in positive characteristic, Theorem 1.1](https://hoyois.app.uni-regensburg.de/papers/motivicsteenrod.pdf), and Bachmann–Hopkins, [Motivic Eilenberg–Mac Lane spaces at the characteristic, v1, Theorems 6.41 and 7.1](https://arxiv.org/html/2611.02320v1). |

For the mod-two proof the cohomology operations act on the reduced cohomology
of the suspended Čech object. The initial construction needs the coefficient
Bockstein, the reduced powers used to obtain the Milnor operations and their
specific suspension and vanishing identities. The odd-prime extension adds
the unstable recognition theorem for the operation of bidegree
`(2b(ℓ−1)+1, b(ℓ−1))` on `H^{2b+1,b}`. Bistable operations and spectrum
endomorphisms are later consumers of the suspension comparisons.

## Chosen models and order of proof

1. Use the native category `Under (⊤_ (Cᵒᵖ ⥤ SSet))` for pointed simplicial
   presheaves on the actual site `C`. Use ordinary simplicial realization weak
   equivalences objectwise at this layer. Form the homotopy category of the
   pointed model, with the Nisnevich and A¹ comparisons on that model. Build
   the homotopy pushouts used by the Nisnevich generators. Empty descent is
   a separate condition. Match the resulting maps to Nisnevich local weak
   equivalences and the actual projections `U × A¹ → U` before using the
   resulting localization as the motivic homotopy category. The ordinary
   square gluing theorem and the bare categorical localization are inputs to
   this step. The strict reduced cone of a strict arrow is constructed using
   a based simplicial interval and its endpoint. Identify it with the
   homotopy cofiber at the model comparison boundary.

   The present presheaf construction takes native site fibers, localizes
   at the resulting stalkwise class, and uses actual pointed cylinder
   projections to test interval locality in that category. To compare
   with the simplicial-sheaf presentation, use the degreewise adjunction and
   the pointed unit, which induces actual fiber isomorphisms. Check that
   sheafification transports the cylinder maps. The essentially small affine
   basis over a quasi-separated base gives ordinary sheafification in the
   universe of the original Yoneda presheaves.

   For enough points, use cofiltered diagrams of pointed étale neighborhoods.
   Reuse `exists_common_nisnevich_refinement` for common refinements and the
   open diagonal of an étale map for equalizing two maps of neighborhoods.
   Pull back a covering sieve and use its actual residue-field lifting to
   prove the hypothesis of `GrothendieckTopology.Point.ofIsCofiltered`. In
   the converse sieve test, lift the identity germ at each scheme point
   with its own residue field. Equality of representatives after refinement gives an
   actual member of the sieve with residue-field isomorphism. The affine
   basis allows the family and neighborhood diagrams to use the original
   value universe. The henselization limit identifies these same points
   when a geometric comparison is needed. Then identify the simplicial and
   motivic equivalence classes and establish the required local replacements
   and homotopy pushouts.
2. Use Mathlib's terminal Čech nerve on `SmoothSite S`. Prove that the
   identity scheme is terminal and obtain finite products from the existing
   binary products. Its augmentation and split contraction must be the
   native maps. Its pointed reduced cofiber is a consumer of step 1. The
   split contraction uses the actual extra degeneracy, independently of
   motivic localization.
3. Use the Nisnevich-sheafified Suslin complex of the reduced transfer torus
   with cohomological shift `[-q]` as the coefficient realization. Align the
   torus and its unit with the native Laurent-open geometry. Port the
   multiplication-by-`n` cone with its coefficient maps and positive
   connecting morphism. The mod-`n` Bockstein is reduction after the integral
   connecting morphism, so its square is zero by the coefficient triangle.
   The native cone-composition triangle identifies the actual insertion,
   reduction and Bockstein in the `n²` coefficient triangle. Define reduced
   cohomology through derived Hom from the reduced free chains and prove
   natural agreement at `U₊` and along the actual cofiber sequence.
   The first coefficient file uses the actual ordinary graph restriction
   and sheafified algebraic-simplex chains. For the transfer enhancement,
   prove identity, composition and mixed graph interchange for the native
   simplex exterior action. Compare its underlying signed complex with
   this same ordinary coefficient.
4. Construct `K(A,p,q)` from the same coefficient complex using Dold–Kan
   and the local derived comparison. Establish coefficient A¹-locality
   using the strict-invariance input over the selected base fields. The
   strict map comparison is obtained by reduced free abelianization,
   sheafification and Dold–Kan, followed by good-truncation factorization.
   For the derived comparison, use the native bijection
   `CochainComplex.IsKInjective.Qh_map_bijective` on a K-injective
   coefficient replacement, and prove that the pointed local model and
   its homotopies give the corresponding morphisms.
   The simplicial suspension comes from the reduced-chain shift. Construct
   `T = A¹/(A¹ − 0)` from the actual Laurent open immersion. The comparison
   with `S_s¹ ∧ (G_m,1)` uses Morel–Voevodsky's simplicial cone roof, and
   the comparison from `(P¹,∞)` uses the actual quotient map. Identify the
   cohomology maps with multiplication by the suspension classes. Use the
   effective-cancellation route for the Tate suspension. In the cancellation
   argument, check the special-fiber cycle Euler-length computation directly
   through the required Tor lengths. Record a separate derived-tensor and
   external-product comparison where a proof uses it.

   The strict roof has common source `tateCone`. Its right leg collapses
   the attached simplicial cone and its left leg collapses the pointed
   affine line. The implemented right-leg proof applies native pushout
   invariance on each fiber. The fiber preserves the Laurent open's
   monomorphism and the actual cone collapse is a realization weak
   equivalence there. The left-leg proof needs invariance of homotopy
   pushouts under the chosen affine-line localization, together with the
   implemented pointed affine-line contraction. For simplicial suspension
   on chains, carry the actual last-vertex maximum contraction of the
   reduced cone through reduced free abelianization and normalization.
   Prove the exact cone-inclusion sequence and identify the resulting
   suspension comparison with the signed chain shift.
5. Compare the finite-correspondence quotient of `A^q/(A^q − 0)` with the
   diagonal representative `K(A,2q,q)` and retain its product and
   tautological class. Establish relative Thom, naturality, and base change
   over smooth bases. These are the first consumers needed for Riou's map
   `K_E → K_(E ⊗ ξ)` for a finite étale torsor and a permutation bundle.
   The total-power construction and the Rost proof are downstream of this
   foundation.
6. For the later odd-prime proof, preserve the derived symmetric powers,
   the scalar action on the diagonal representative, and the bar filtration
   for its simplicial delooping. The target application is the one-dimensional
   kernel in Voevodsky 2011, Proposition 2.6, used to identify the Rost
   symmetric-power operation with a nonzero multiple of `β P^b`. Hu's
   finite-linear-quotient comparison is a separate candidate for the
   smooth-site restriction at the diagonal representative. Its proof and
   actual-map compatibility are pending review. The stable spectrum layer
   is a separate product with a subsequent comparison to these constructions.

## First independent Lean slices

| Slice | First write owner | Module scope |
| --- | --- | --- |
| Pointed presheaves and objectwise equivalences | Localization | `Colib/Topology/Realization/MorphismProperty.lean`, `Colib/CategoryTheory/Sites/Simplicial/PointedPresheaf.lean` |
| Terminal smooth scheme and augmented Čech nerve | Čech | `Colib/AlgebraicGeometry/Sites/Smooth/FiniteProducts.lean`, `Colib/AlgebraicGeometry/Sites/Smooth/Cech.lean` |
| Generic finite coefficients | Coefficients | `Colib/Algebra/Homology/CochainComplex/FiniteCoefficients/Basic.lean` |
| Actual affine line and torus open complement | Tate | `Colib/AlgebraicGeometry/Scheme/PolynomialLaurent/TatePair.lean` |
| Integration and shared documentation | Principal | This plan, root enrollment and common Library metadata |

Authors keep their proof, compiler feedback and repairs together. Independent
ready targets are sent in one remote Lake build. One remote workspace owner
coordinates source sync and uses the existing shared resource pool. The prepared
seed has the exact pins and its prior results are cache inputs. The task's new
allocation is subject to the server's storage reserve. Keep proof feedback
incremental, then run the applicable Colib checks once for the integrated slice.
Report exact checked modules and distinguish them from pending comparisons.
Production uses the project's three allowed axioms and native source enrollment.

## First implementation checkpoint

The initial Linux build completed with eight concurrent frontends at peak
on the locked source basis. The task workspace is private and was prepared
from clean copy-on-write dependency sources. The native Mathlib cache
supplied the selected import roots. The first six-root build is recorded
under run `remote-5b83b28e19304f93a4cd09eac176b275`, with source digest
`99a744484e5933054a78e37745c9d77e5c2e53a85e36399104dcc04c90c2a9ff`.
Further exact Linux leaves cover the pointed Čech cofiber, the Tate quotient,
reduced normalized chains, reduced hypercohomology, the generator maps and
the formal stalkwise and interval localizations. The integrated metadata
build has its own source snapshot. The strict Nisnevich square maps and empty
descent induce isomorphisms on every native site fiber, and the formal
affine-line localization inverts these and the original affine-line
projections. Degreewise left exact sheafification follows from ordinary
type-valued sheafification. The coefficient composition triangle is
distinguished in the homotopy and derived categories, and the associated
degree-one operation on reduced hypercohomology squares to zero.

The reduced transfer torus and ordinary Suslin coefficient use the native
correspondence groups and the scheme universe of the pointed Yoneda
presheaves. Their same-universe Linux build passed in
`remote-8f8d8cf23f8d428aa7dceb4c21c36038` at source digest
`9965b2d932d045bfab0a860c1f2386e6bae75ccc6cb2e548ff5c417f6070e157`.
The transfer build graph includes 5,685 Stacks modules from the pinned Linux
checkpoint. The exterior support geometry and additive extension passed on
the same toolchain. The exact graph and identity comparisons passed in
`remote-caf557e69de94b9d893d81381b93197d` at source digest
`ae5d2a182dbd39ab39800faeffd37e668a7fdea85b5cc8272b5f1acfdb43ecba`.
Exterior composition and mixed graph interchange still need their native Tor
and multiplicity comparisons. These are proof dependencies for the transfer
enhancement.

The final affected Linux batch
`remote-41e5661b379d4323adedc63553df9e7f` used source digest
`4c68570dff5f4efb1660b024bf620c051b5a4785c7ba8795ca2619b014756863`.
Ten requested roots and their changed prerequisites passed. Twenty-one
frontends succeeded with eight active at peak. This includes the native
same-universe site sheafification, the original generator inversion, the
Tate cone-to-quotient comparison, and the reduced hypercohomology and
square-zero Bockstein on the actual finite motivic coefficient complex.

For exterior composition, use the affine-space chart of the simplex. The
triple parameter change to the two consecutive differences and the last
parameter is `MvPolynomial.tripleDifferenceEquiv`. In those coordinates
the two pulled supports have ideals `(I_W,u)` and `(I_V,v)`. For the Tor
comparison, extend a resolution of the original first quotient and tensor
with the Koszul complex on the (u)-variables. After tensoring with the
second quotient, the (u)-variables remain polynomial variables, so this
Koszul complex resolves the quotient by these variables. Its augmentation
is a quasi-isomorphism and leaves the original Tor with polynomial extension
in the last parameter. The native Lean proof
must identify the actual support maps in these coordinates, then transport
the generic lengths and residue degrees in finite pushforward. For mixed
graph interchange, the same parameter translation uses the actual simplex
arrow and leaves the original graph incidence calculation.

## Source locators

- Morel and Voevodsky, §2.3, Definition 3.1 and Remark 3.3, and §3.2,
  Lemma 2.15, Proposition 2.17 and Theorem 2.23.
  [A¹-homotopy theory of schemes](https://numdam.org/item/PMIHES_1999__90__45_0/)
- Voevodsky, §2, Theorems 2.1 and 2.4 and equation (2.9).
  [Reduced power operations in motivic cohomology](https://numdam.org/item/10.1007/s10240-003-0009-z.pdf)
- Voevodsky, §7, proof of Proposition 7.1, and Appendices A and B.
  [Motivic cohomology with Z/2-coefficients](https://numdam.org/item/10.1007/s10240-003-0010-6.pdf)
- Voevodsky, §§3–4 and the effective-motive consequence.
  [Cancellation theorem](https://arxiv.org/abs/math/0202012)
- Riou, §§1–2 and §3.7.
  [Opérations de Steenrod motiviques](https://arxiv.org/abs/1207.3121v1)
- Voevodsky, Theorems 2.76, 3.25 and 3.32.
  [Motivic Eilenberg–Mac Lane spaces](https://arxiv.org/abs/0805.4432)
- Voevodsky, §§2–3 and §5.
  [On motivic cohomology with Z/ℓ-coefficients](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/on_motivic_with_Zl_published.pdf)
