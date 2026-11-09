# Quillen and Motivic migration

The initial pilot selected three boundaries from the proposed integration. The table
records that starting scope; the sections below describe subsequent results.

| Boundary | Initial pilot surface | Work identified at the pilot |
| --- | --- | --- |
| Finite-module K₀ | Categorical dimension equivalence over a field | Compare the original Quillen degree-zero map and its exact-category presentation |
| Milnor K₂ | Equality of the two Steinberg relation spans and the symbol-preserving tensor comparison | All-degree tuple symbols, norms, residue maps and Quillen field comparisons |
| Finite-flat coefficients | Affine finite-algebra length-degree sum | Construct the original finite-flat spans and prove their faithful cycle and composition equations |

The initial release is a source-indexed reference-indexed pilot. The Quillen and Motivic libraries
remain migration sources at the recorded commits below.

- Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
- Motivic a6805c4a87cdfd7717dd7a94039246a167f15380.

Extend the closed pilot one mathematical chain at a time. Exact categories and shared module
foundations precede scheme K/G-theory and perfect-complex localization. Finite correspondence
geometry precedes transfers, ordinary Nisnevich hypercohomology and strict invariance.
Record cohomological degrees, coefficient universes, signs, canonical maps and actual
conditions at each endpoint.

Use the pinned Mathlib and Stacks objects and interfaces directly. Add missing mathematics
at its native owner; do not maintain legacy models or compatibility layers. Genuine comparisons
between distinct mathematical constructions retain their precise hypotheses and actual maps.
Historical implementation attribution is preserved without retaining an Aglib source inventory
or making Aglib a dependency. Actual consumers determine the incremental validation scope.
Source correspondence and mathematical review retain their own status.

The first Library release demonstrates this process on twelve entries. The amount of
further migration is measured by the actual proof and interface repairs for subsequent slices.

## Waldhausen additivity milestone

The actual unnormalized S-construction now supports the complete original
canonical K-map additivity formula, including degree zero. The ordinary
unreversed subdivision endpoint is a proved realization homotopy equivalence;
compact-source lifting for the actual realization-product comparison gives the
original product K-map equivalence. Coproduct is the existing group law, which
is proved commutative also in K-zero. Exactness, cofiber squares, relative
cofibrations, target binary coproducts and the source universe bounds are retained.
See [the chosen-model and source crosswalk](migration/waldhausen/README.md).
A strict chosen-zero S-model comparison and broader Quillen-Waldhausen comparison
remain separate work.

## Objectwise-finite Quillen Resolution

The resolving-subcategory theorem now uses actual finite admissible towers,
length-one comma contractions and the actual countable nerve union. Resolution
lengths need not have a common bound. The resulting Q-space equivalence and
all-degree K-equivalence retain the original inclusion maps. See the
[precise native-model and source scope](migration/resolution/README.md).
General filtered realization is now available as part of the later Serre
localization proof below. This Resolution result does not close the entire
Quillen migration.

## Canonical Grothendieck–Quillen K-zero comparison

The original Grothendieck-to-Quillen K-zero map is now proved injective and
bijective on the existing realized Q-category and its original zero basepoint.
The proof establishes faithfulness of the original groupoid-completion functor
using actual finite-skeleton decoders and compact relative homotopies. See the
[native proof and source scope](migration/quillen/kzero-comparison.md). This does
not claim a higher K-group comparison or completion of the Quillen inventory.

## Classical Quillen devissage

Actual finite filtrations now contract the inclusion comma categories through
the layer poset. The resulting classifying-space and all-degree K-equivalences
retain the actual inclusion maps and canonical zero basepoint. The full
subcategory is intrinsically abelian: no extension-closure or uniform-length
hypothesis is added. See the [native proof and source crosswalk](migration/devissage/README.md).
This does not assert a Q/S comparison or finish the historical Quillen inventory.

## Canonical connective Serre localization

The original normalized quotient fiber comparison is now a weak homotopy
equivalence on every component and at every source basepoint. Its actual group
comparison gives the connective localization long exact sequence, including
the K-one to K-zero boundary and terminal surjection, under only the original
small abelian-category and Serre-class hypotheses. Inclusion and quotient are
the original K-maps; the boundary retains its native path-space convention.

The supporting complete Theorem B retains both actual comma comparisons under
transition homotopy equivalences. Arbitrary filtered simplicial realization
invariance requires neither monicity nor countability. These are complete
mathematical results, not replacements for the original objects or conditional
localization adapters. See the [precise proof and evidence scope](migration/serre/completion.md)
and [Library integration record](migration/serre/integration.md). Negative
K-theory and the more general weak-transition form of Theorem B are not claimed by that Serre item.

## Original-map Waldhausen fibration and approximation

The fibration theorem now proves weak equivalence of the original canonical
acyclic-to-homotopy-fiber map, including its full reversed nullhomotopy and
independent object and morphism universes. Coarse two-out-of-three, extension,
exact base-category joint-cylinder data and its second-endpoint section are
retained. Actual relative rows and proved weak-cartesian bar assembly discharge
the global fiber comparison. See the [native scope and review boundary](migration/quillen/waldhausen-fibration.md).

Approximation proves weak equivalence of the unchanged delooping map from
App1/App2, exactness, target two-out-of-three and genuine source joint-cylinder
data. Its group equivalence has the original canonical KMap as its forward
map in every nonnegative degree, including K-zero. It assumes no row-equivalence
or homotopy-inverse premise. These results do not supply a strict S-model
comparison, a Quillen-Waldhausen comparison or nonconnective K-theory.

## Prescribed canonical-fiber component translation

COL-0296 retains the strict left-translation equivalence on actual localization
loop fibers and the specified identity-cofiber suffix, together with both literal
values on the transposed original canonical-fiber object loop. The entire
reversed fiber track and independent category universes remain. The prefix needs
no zero-morphism instance; only the suffix/component step adds one. No fibration
or canonical-fiber-map weakness premise is imposed. See the
[exact construction and source crosswalk](migration/quillen/waldhausen-canonical-fiber-component.md).
The integrated COL-0296--COL-0301 sources and tests at
[`ea4dc640a5bec4e7eb49e0268c08c9f1fed1fc01`](https://github.com/kangxyz/colib/commit/ea4dc640a5bec4e7eb49e0268c08c9f1fed1fc01)
passed the repository's native checks in
[CI run 42435539991](https://github.com/kangxyz/colib/actions/runs/42435539991).
Native validation, `author_checked` source correspondence and independent
mathematical review remain distinct facts.

## Prescribed cofiber-prism boundary and normalization

COL-0297 retains the full data-valued cofiber-prism boundary, the exact reversed
canonical-fiber quotient prefix and the prescribed identity-cofiber suffix.
Gluing proves quotient acyclicity. The boundary and prefix retain independent
parameters and their distinct boundary-time and loop-time concatenations.
Normalization compares only degree-one induced maps, not equality of suffix
paths; no fibration, canonical-comparison weakness or Laurent-sign claim is added.
See the [exact construction and source cuts](migration/quillen/waldhausen-cofiber-boundary.md).
The integrated sources, tests and attributes passed the native CI recorded above;
this supersedes their uncompiled preparation status.

## Original automorphism K-one and whole change-of-weak transport

COL-0299 retains the specified weak-object composition cube and whole-path
homotopy, independently normalized weak-endomorphism and automorphism K-one
classes, and both unrestricted canonical KMap naturality theorems. Composition
keeps the original reversed multiplication order. Fine-to-coarse transport
preserves entire bisimplex families, displayed cofiber tracks, weak-arrow squares
and identity-cofiber suffixes, with component naturality in every degree.
Independent parameters, universe bounds and both cofiber certificates remain;
no scalar, Laurent or boundary-sign theorem is asserted. See the
[exact construction and source scope](migration/quillen/waldhausen-automorphism-kone-transport.md).
The integrated sources, tests and attributes passed the native CI recorded above.
The earlier source-only preparation record is not the current validation status.

## Matsumoto's theorem for K₂ in characteristic zero

The completed source chain gives characteristic-zero additive equivalences from
the native Milnor K₂ group to actual right-projective Quillen K₂ and the literal
upper finite-module `SmallK.{u+1} 2`. Their forward homomorphisms are the original
Milnor-to-kernel-to-Quillen composites. Fiber perfectness, kernel generation and
the detector are proved inputs, not additional endpoint hypotheses. Both
directions commute with the original field-extension maps; the negative
normalization is minus the positive inverse.

The positive ordered scalar-unit-product marking holds over every field,
with a `ZMod 5` regression. Bijectivity retains `[CharZero F]`.
Finite realization geometry now uses native `Convexity.StdSimplex` coordinates directly.
Earlier candidate endpoints and regressions passed focused strict compilation
and native QA within their recorded scopes. The Lean 4.35 integration is published
at `0fd43f0253d6ff441fbc3e82420a0573ad694310`, whose original whole-library
[CI run](https://github.com/kangxyz/colib/actions/runs/42373233801) passed build,
tests, native lint, axiom audit and Library checks. This exact-commit result does
not certify later descendants. See the
[exact comparison and verification scope](migration/quillen/field-k2-comparison.md),
[algebraic map](migration/quillen/field-k2-native-kernel.md), and
[stable-fiber proof](migration/quillen/field-k2-stable-fiber.md).

## Original-map Gillet-Waldhausen

The native bounded-complex proof retains the actual abelian ambient, term bounds,
cofibrations, quasi-isomorphisms and canonical degree-zero single KMap. Its group
equivalence includes K-zero and the original object/hom universe bounds. Exact
filtrations, finite Euler decomposition, filtered-union coverage and the actual
identity-cone cylinder supply the proof, without a theorem-shaped input.
See [the exact scope and dependency ownership](migration/gillet-waldhausen.md).

## Dense Waldhausen cofinality

The actual dense full inclusion now has its original positive K-equivalence,
all-degree injectivity and degree-zero exact tail. A genuine complement grading,
finite replacement, actual row-grade nerve comparison and the proved original
fibration supply the proof. Coarse K-zero remains the true homotopical endpoint. The actual value map now
identifies it with complement classes, retaining object generators and the
original matching-universe map.
See [the precise native scope](migration/quillen/waldhausen-cofinality.md).

## General Waldhausen Grothendieck K-zero

The original object-loop comparison is an equivalence from the actual free
abelian presentation by weak arrows and cofibration pushouts to homotopical
Waldhausen K-zero, including independent object and morphism universes. No
cylinder or factorization hypothesis is added to this comparison. Actual
edge-path generation supplies surjectivity, and the realized universal grading
is its inverse. Original exact-functor KMaps commute with the comparison.

With genuine target factorization, the actual coarse value map identifies
K-zero with the quotient by the original exact-functor image. Its composite
with the unchanged changeWeak KMap is the literal quotient, and its kernel
and surjectivity give the exact original K-zero tail. No higher-degree
image-quotient or spectrum conclusion is inferred. See the
[canonical maps and verification scope](migration/quillen/waldhausen-grothendieck-kzero.md).

## Whole based-additivity transformation square

COL-0301 retains the actual parameterized square
between the original based-additivity homotopies. Four complete faces and the
entire chosen-zero surface retain independent times, the once-reversed prefix,
half/quarter/quarter clock and quotient-first sum. The two cofibration sequences,
three pointwise weak transformations, both commuting squares and binary
coproducts are explicit; no extra fibration, cylinder or strict-zero premise is
added. See the [source and verification boundary](migration/quillen/waldhausen-based-additivity-square.md).
The integrated sources and tests passed the native CI recorded above. This is
general theory, not a scalar, support, Laurent or Bass conclusion.

## Compact coproduct cubes and whole null coherence

COL-0302 retains the actual unique compact product lifts, complete cube boundaries,
based coproduct unit paths, quotient-first spatial separation and supplied-null
coherence. Change of weak equivalences preserves whole paths and independent
times. The normalized endpoint retains its original explicitly supplied whole
Theta comparison; this does not construct geometric scalar data or prove a
scalar boundary formula.

The seven original source files have twelve native production owners and seven
original regression modules. The [precise hypotheses, source correspondence and
validation scope](migration/quillen/waldhausen-compact-coproduct-coherence.md)
record the complete contribution and its separation from the later scalar topic.

## Original S-construction composition triangles

The actual two-transformation simplicial triangle retains the original cylinders
on all three faces, including the genuine composite. Its full zero-vertex family
is constant under the three explicit chosen-zero equalities. The sole zero-simplex
definition has its lower simplicial owner, with existing K-theory clients unchanged.
See the [exact source and scope](migration/quillen/waldhausen-composition-triangle.md).
This does not establish iterated-S or spectrum compatibility.

## Coherent Waldhausen endotransformation tracks

The actual finite S-prespectrum, whole structure-compatible weak-transformation
homotopies and relative composition retain the original KMap, basepoints and
independent parameters. The genuine zero endotransformation contracts the
original normalized self-track in a grading-coarse target; the null-loop
endpoint retains both supplied null legs. Native category and path objects
have one owner. COL-0276--COL-0278 record the complete contribution and its
precise coherent-track scope. See the
[source and verification boundary](migration/quillen/waldhausen-coherent-endotransformations.md).

## Genuine connective Waldhausen Omega-spectra

Every actual iterated S-construction loop structure map is a complete weak
homotopy equivalence, including path components and every finite based
homotopy set. The proof uses the genuine added-initial-row contraction,
higher first/tail additivity and the full actual path-fiber comparison.
COL-0282 packages the same prespectrum and exact-functor maps as an
Omega-spectrum without new structural hypotheses. Original KMaps and
independent category universes are retained. See the
[actual maps and verification scope](migration/quillen/waldhausen-omega-spectrum.md).

## Bounded-complex resolution bridge

An actual bounded native complex quasi-isomorphic to a single object now yields
a finite admissible resolution in any replete kernel-closed class containing
zero. Lifting the resulting tower into an exact full subcategory retains all
ambient maps and its length. Arbitrary small-model functoriality also retains
the canonical K-maps. See the [G-localization and resolution scope](migration/scheme-kg/README.md).
The scheme-specific comparison is developed in the separate
[native scheme K/G slice](migration/scheme-kg/native-scheme-comparison.md); it is not
a conclusion of the bounded-resolution foundation alone.

## Actual-target and finite-module G-localization

The canonical connective Serre sequence now transports to the actual specified
target and to the original small-model K-map. For a commutative Noetherian ring,
the literal native finite-module functor at any multiplicative set gives the
full connective sequence, including the homotopical G-zero tail. Support is
annihilation by one denominator; for powers of an element this is one uniform
natural power. The existing fraction-field K-map is retained definitionally.
See the [exact scope and source crosswalk](migration/scheme-kg/fraction-localization.md).
This arbitrary-set result by itself does not identify principal supported
G-theory with G of the quotient ring or prove general scheme-open localization.

## Principal closed/open G-localization

Actual finite-module restriction along R to R/(r) is fully faithful with essential
image the r-annihilated modules. Inside the existing supported small category,
multiplication by r constructs finite image filtrations with such factors.
Classical dévissage therefore gives G(R/(r)) equivalent to principal supported
G-theory, with forward map compatible with the original quotient-restriction
smallKMap. The transported original boundary gives the full connective
closed/open sequence, including G-zero. No regularity or nontriviality hypothesis
is added. See the [precise native scope](migration/scheme-kg/principal-closed-localization.md).

## Native scheme K/G-theory and regular comparison

Native vector bundles and coherent module sheaves now carry the original upper
small-model connective K-groups. The literal inclusion gives the canonical K-to-G
map, and actual open restriction obeys strict identity and composition laws and
commutes with that comparison. On a quasi-compact regular scheme with the
resolution property, native Stacks perfectness and bounded replacement discharge
actual finite-resolution hypotheses, proving the canonical comparison is an
equivalence in every nonnegative degree. No separatedness, uniform dimension or
global projectivity assumption is added. See the
[precise geometric scope and literature](migration/scheme-kg/native-scheme-comparison.md).
This does not assert general scheme-open K-localization or nonconnective K-theory.

## Native perfect open support and scalar-cone inputs

Actual restriction along any open immersion preserves native Stacks perfect
complexes. Open-detected weak equivalences give the relative coarse structure
without changing its ambient monomorphism cofibrations. Its genuine acyclic
subcategory is exactly equivalent to the native supported category, preserving
the original inclusion and all nonnegative K-maps. The actual scalar cone is
supported when the scalar restricts to a specified unit; native rank-one and
positive Laurent coordinate comparisons keep the forward T orientation.
See the [source and exact scope](migration/scheme-laurent/native-open-support.md).
This foundation by itself does not prove fine-open localization or the
scalar/Laurent connecting-boundary formula. The relative fiber theorem is the
next separate complete slice below.

## Native relative-open perfect fiber and exact sequence

The actual native `Cone(id K) ⊞ L` joint cylinder supplies the structural
factorization and second endpoint section for arbitrary open immersions.
Together with the proved extension axiom, this gives the original canonical
fiber weak equivalence and all recurring positions of the connective supported
long exact sequence. Degree zero surjects onto the relative coarse K-group,
without identifying it with fine perfect-complex K-theory of the open. See the
[exact scope and validation boundary](migration/scheme-laurent/native-open-fiber.md).

## Native scalar cofiber and whole based-additivity square

COL-0303 proves the original scalar cofibration sequence on native perfect complexes
and specializes the full based-additivity transformation square to its literal
identity-to-scalar sequence map. The actual signed quotient, categorical cofiber
comparison, four whole faces and two-time chosen-zero surface are retained.
No scalar regularity is assumed. This square alone does not identify fine-open
localization or compute the connecting boundary; the relative scalar boundary is
the separate COL-0304 result below. See
[the native objects and source scope](migration/native-scalar-cofiber-square.md).

## Native forward scalar supported boundary

COL-0304 identifies the original relative connecting homomorphism on the
independently defined forward scalar K₁ class with the positive supported K₀
object class of its actual signed mapping cone. The data are an arbitrary open
immersion, a native perfect complex, a global scalar, a specified unit on the
open, and equality of the restricted scalar with that unit. The actual cofiber
prism, fine return path, iterated fiber and component transport retain the first
inverse, which cancels the existing transpose inverse in the connecting map.
No quasi-compactness, quasi-separatedness, regularity, Noetherianity,
nonzerodivisor or supplied boundary-compatibility hypothesis is added.
This is not fine-open localization, a Laurent-coordinate or Bass-sign result,
or an all-degree scalar boundary formula. See
[the native construction, orientation and validation scope](migration/quillen-scalar-supported-boundary.md).

The individual COL-0302, COL-0303 and COL-0304 sources passed local native
compilation and independent source reviews. The complete integrated scalar topic at
[`5eca54b0b939d2cd8ca2674c4bbd01e1f93528ab`](https://github.com/kangxyz/colib/commit/5eca54b0b939d2cd8ca2674c4bbd01e1f93528ab)
passed the `Build` and `Test, lint and axiom audit` jobs in
[CI run 42440827329](https://github.com/kangxyz/colib/actions/runs/42440827329).
These checks do not assert any later fine-open or nonconnective result.

## Native global-unit K-one and forward scalar restriction

COL-0305 defines the independent fine K₁ class of the actual native global-unit
automorphism and proves object-isomorphism invariance, inversion and compatibility
with canonical fine restriction. For an arbitrary open immersion and a scalar
restricting to a specified unit, the original coarse restriction K-map sends the
independently defined forward scalar class to this fine unit class. Rank one uses
the actual structure-sheaf restriction isomorphism.

Affine polynomial/Laurent comparisons apply over every commutative ring, including
the zero ring. Native relative Laurent comparisons apply over every scheme and
retain the actual forward `T 1` coordinate in the existing Stacks base-change
presentation. The scalar-cofiber class restricts to the inverse unit class; this
inverse is not discarded. See
[the actual maps, source correspondence and scope](migration/quillen-global-unit-comparison.md).

This is a degree-one class comparison, not a coarse-to-fine K-equivalence,
fine-open boundary, zero-section boundary, Bass sign or all-degree scalar formula.
The COL-0305 source and its affected consumers have passed local native compilation
with exact source and direct-dependency artifact verification. Independent source
review has separate evidence. Candidate
[`d67b69cc1289c326508f481f8aca2758946c7f19`](https://github.com/kangxyz/colib/commit/d67b69cc1289c326508f481f8aca2758946c7f19)
passed the `Build` and `Test, lint and axiom audit` jobs in
[CI run 42444372165](https://github.com/kangxyz/colib/actions/runs/42444372165).
It is included in main at the later generic-topic commit recorded below.

## Native coarse exactness of the original joint cylinder

COL-0306 constructs JointData for the reflexive coarse structure from the existing fine-exact
joint data and coarse two-out-of-three. Actual endpoint pushouts and coarse gluing prove source
weakness; the actual projection square proves middle weakness. Native extension postcomposition
preserves cofibrations and pushouts, retaining the entire original functor, endpoints and
projection. Generic and actual native perfect-open regressions exercise the existing coarse row
factorization. This is a general prerequisite, not dual approximation or fine-open localization.
See [the source crosswalk and exact scope](migration/native-coarse-joint.md).

## Native dual approximation

COL-0308 constructs the full original S-grid reversal for structurally compatible dual
Waldhausen categories and transfers ordinary approximation to the original dual K-map. The
inverse-image theorem preserves the literal functor and strict fine incoming equations without
assuming fine reflection; genuine coarse joint exactness comes from COL-0306. This is a general
categorical prerequisite, not a geometric qcqs fine-localization theorem. See [the exact source
crosswalk and scope](migration/native-dual-approximation.md).

## Native comma and weak-arrow factorization

COL-0309 migrates all nine original comma, opposite and weak-arrow files in its source crosswalk
to their distinct category-theory and K-theory owners. The actual fine weak-arrow objects,
stored arrows, component pushouts and relative inverse-image structures are retained. The
identity-arrow diagonal and source induce inverse canonical KMaps in every nonnegative degree,
including K-zero; the unchanged original KMap factors through the actual target map. This proves
the first-leg equivalence, not target approximation or geometric fine localization. The generic
opposite joint-cylinder continuation is COL-0310 below; scheme-specific compatibility and
geometric incoming lifts remain open. See [the source crosswalk and exact
scope](migration/native-weak-arrow-factorization.md).

## Native opposite weak-arrow joint data

COL-0310 retains the original generic construction of exact joint data on actual opposite weak
arrows from two component joint functors, their given natural isomorphism and the three endpoint
coherence equations. Source, middle, component cofibrations, endpoint maps and the original
factorization are unchanged. This does not supply a scheme-specific comparison or strict
preservation of independently chosen cofibers. See [the source crosswalk and exact
scope](migration/native-weak-arrow-joint.md).

## Dual and weak-arrow topic boundary

COL-0306, COL-0308, COL-0309 and COL-0310 together supply generic categorical machinery. The
compatible dual S-construction and realization, strict incoming dual approximation,
inverse-image lift KMap bijection, actual weak-arrow factorization and coherent opposite joint
data retain their original hypotheses and maps. The component joint data, given natural
isomorphism and all three endpoint equations remain explicit inputs. A comparison between
independently chosen cofibers requires its canonical isomorphism and is not asserted to be
definitional equality.

This topic does not establish actual perfect-complex duality, scheme-specific joint
compatibility, derived-image approximation or qcqs fine localization. COL-0307 geometry and its
drafts are not included. The source crosswalks, local Lean compilation and independent component
reviews are separate evidence. The integrated generic topic at
[`8fc02d4a4fdd9b82b610166143b75310184b624e`](https://github.com/kangxyz/colib/commit/8fc02d4a4fdd9b82b610166143b75310184b624e)
passed the `Build` and `Test, lint and axiom audit` jobs in
[CI run 42447592408](https://github.com/kangxyz/colib/actions/runs/42447592408)
and is now included in main. These checks cover the generic topic, not the later native
perfect-complex foundations below.

## Native opposite perfect-complex coherence

COL-0311 constructs the actual opposite complex and exact-category structures, original
degree-reversing joint cylinder, and coherent natural comparisons under exact additive functors.
Native perfect open restriction has all six endpoint equations and actual opposite weak-arrow
joint data. The old complex-subcategory source loses only two unused K-theory imports; its four
declarations are unchanged. No scheme-specific coherence hypothesis remains. See [the exact
source crosswalk](migration/native-opposite-complex-coherence.md).

## Native honest open-derived image

COL-0312 uses the honest native derived image of actual globally perfect complexes.
Derived-isomorphism invariance, perfectness, weak cospans and literal corestriction require no
roof hypothesis. With the explicitly stated `OpenDerivedImage.HasDerivedRoofs j` input, actual
triangles and short exact sequences supply closure, the ambient Mono/QuasiIso Waldhausen
structure, exact inclusion and corestriction, and strict incoming factorization. Two actual
homotopy pullbacks preserve the chain-map equations and kernel endpoints. No derived equality is
silently treated as chain-map equality. The separate unconditional K-zero theorem identifies
coarse and fine restriction ranges; it does not prove surjectivity onto K-zero of the open. See
[the exact source crosswalk](migration/native-open-derived-image.md).

## Native bounded finite locally free foundations

COL-0313 uses native `boundedFiniteLocallyFreeComplex` for the original global term bounds and
termwise finite local freeness. Actual zero, isomorphism, short exact extension, shift, single
and signed-cone closure give its exact/Waldhausen structures, vector-bundle single inclusion,
native perfect inclusion, canonical KMaps, actual joint cylinders and compatible opposite
inclusion endpoints. All schemes are allowed. The distinct global finite-free-retract
`IsStrictlyPerfect` predicate is not substituted. See [the exact source
crosswalk](migration/native-bounded-vector-bundle-complexes.md).

## Native relative corestriction approximation

COL-0314 constructs the honest image opposite structures, coherent joint comparison with all six
endpoints, actual opposite weak-arrow joint data and genuine strict incoming lifts. Given
exactly `OpenDerivedImage.HasDerivedRoofs j`, the original relative corestriction K-map is
bijective in every nonnegative degree. Its induced multiplicative equivalence has that literal
K-map as forward function, and actual image inclusion recovers `perfectOpenKRestrict`. No
categorical approximation or joint-compatibility premise remains. This is not ordinary outgoing
App2 or a proof of geometric roofs, complement/density, or qcqs fine localization. See [the
actual maps and source crosswalk](migration/native-open-image-approximation.md).

## Native perfect-foundations and image-approximation topic boundary

COL-0311 through COL-0314 supply native foundations and actual image approximation conditional
on geometric roofs, not the final geometric localization theorem. COL-0307 geometric roofs and
complement/density, strict-to-perfect K-equivalence, Q/S and Gillet-Waldhausen comparisons, and
final qcqs fine-open localization remain outside this topic. The explicit global-perfect-model
roof input is not asserted to have been discharged. Local native compilation and independent
component mathematical/source reviews are separate evidence. The integrated native topic is
now in main at [42c036f91db8f594ca100d74a3afe5bef4fefdd6](https://github.com/kangxyz/colib/commit/42c036f91db8f594ca100d74a3afe5bef4fefdd6).
Its candidate [CI run 42451971044](https://github.com/kangxyz/colib/actions/runs/42451971044)
and main [CI run 42453718671](https://github.com/kangxyz/colib/actions/runs/42453718671)
completed successfully. Those checks do not validate the subsequent topic below.

## Conditional native honest-image cofinality

COL-0315 constructs actual chosen-coproduct comparisons, zero-pushout short exact sequences,
dense closure and exact flattening. Under precisely HasDerivedRoofs and actual-complex
HasPerfectComplements, the original inclusion and relative restriction are injective in every
connective degree and bijective in positive degrees. Degree zero identifies the actual fine
restriction range, not all K-zero of the open. No density, joint-data, approximation or
K-equivalence premise replaces those constructions. See [the exact source
crosswalk](migration/native-open-image-cofinality.md).

## Actual higher scalar cubes

COL-0316 constructs the original two-time scalar additivity cube on each positive-dimensional
generalized loop. Four whole faces, actual fine paths, their four corners, and the once-reversed
oriented boundary interpolation are proved on the unchanged coordinates. No scalarTheta is
supplied as an input. See [the actual cube
crosswalk](migration/native-scalar-cube-coherence.md).

## Actual scalar normalization and canonical fiber

COL-0317 constructs actual fine projection and canonical null tracks, distinct first and right
subdivision restrictions, canonical pair and sum cylinders, the normalization square and actual
normalized endpoint. The whole canonical fiber cube equals the canonical acyclic-to-fiber map.
This closes the normalization/lift subtopic; COL-0320 below separately supplies actual
prescribed return and connecting comparison. COL-0324 below supplies prespectrum operation identification; input descent
and the global higher scalar formula remain separate. See [the exact normalization
crosswalk](migration/native-scalar-fiber-normalization.md).

## Conditional connective localization and image prespectrum

COL-0318 retains the actual fine boundary, its relative composite and uniqueness, three
recurring exact positions, the K1-to-K0 tail and its surjective actual-image endpoint. The
actual coarse-to-fine prespectrum map has positive stable bijections, degree-zero injectivity
with exactly the global restriction image, and negative vanishing. The canonical
acyclic-to-coarse-fiber map is a stable equivalence. HasDerivedRoofs and actual-complex
HasPerfectComplements remain the exact geometric inputs. COL-0319 below separately supplies
coherent supported-spectrum transport. Global open-pair naturality and the complete TT Section
5.1 assembly are not asserted by COL-0318. See [the original maps and literature
crosswalk](migration/native-connective-open-localization.md).

## Actual supported-spectrum transport

COL-0319 constructs strict chosen-zero inverse prespectrum maps between the original supported
and acyclic categories, then transports the actual canonical fiber map. Projection, every
original nullhomotopy path and both structure parameters are retained. Canonical zero rebasing
has an actual coherent comparison, and the whole level-one map recovers the original supported
fiber K-map through the existing homeomorphisms. This supported-to-relative-coarse-fiber theorem
requires only an arbitrary open immersion, with no geometric roof/complement premise. The
support category consists of native perfect complexes on X acyclic on U, not perfect complexes
on the closed complement. See [the full supported-spectrum
crosswalk](migration/native-supported-spectrum-transport.md).

## Actual scalar return and connecting comparison

COL-0320 constructs the actual fine return and exact reversed terminal word on every original
subdivision cube. The original square proves its inverse inclusion/projection class, while the
two inverse-prefix cancellations, constructive associators, source transport and unpadding
supply an explicit whole-boundary homotopy to the canonical fiber map of the actual acyclic
scalar cone. The original connecting map sends this prescribed return class to the canonical
fiber K-map of the scalar cone K-map, with positive cone sign, including n = 0. All endpoints,
both times, full stored canonical-null paths and spatial boundary are retained. No filler or
comparison is assumed. This constructs the prescribed return class. COL-0324 below identifies it with the
prespectrum scalar operation; arbitrary-input descent remains separate. See [the complete return
crosswalk](migration/native-scalar-return-comparison.md).

## Connective localization and scalar topic boundary

TT Section 5.1, printed pages 337-338, is connective proto-localization with the corrected
K-zero-image target; Section 5.2.2 records the K-zero extension obstruction. TT Section 7.4,
printed page 365, is the later Bass nonconnective theorem, with K-theory on X supported away
from U rather than K-theory of the closed complement. The verified [published
article](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Thomason-Trobaugh.pdf)
is a source locator, not a claim of a newly downloaded or hashed PDF. Native negative-group
vanishing is the existing actual Omega/stage-path-connected proof; integer grading alone is not
Bass delooping. Actual qcqs roof/complement existence, comparison with a separately prescribed
image-cover spectrum, global open-pair naturality
and arbitrary-input descent/global formula remain separate. COL-0321 and COL-0324 below
supply the generic operation and its actual scalar identification. The relative boundary keeps
+[signedCone], distinct from the T-first Bass forward Laurent-unit convention [T] = -[O]. Local
native compilation, source correspondence and independent component review are distinct
evidence. COL-0315 through COL-0320 are published at
[f0fbeb48b5b7cbd6bdebbfbf969921a827c112ec](https://github.com/kangxyz/colib/commit/f0fbeb48b5b7cbd6bdebbfbf969921a827c112ec);
its exact-source candidate [CI run 42463812889](https://github.com/kangxyz/colib/actions/runs/42463812889)
passed. That evidence does not validate the later scalar-operation topic below.


## Actual generic self-track operations

COL-0321 constructs the finite homotopy-class operation, its additivity in input degrees
at least two, actual successor inverse sign including Pi-one, and signed stable-colimit
operation in every integer degree. The actual Waldhausen K-operation includes K-zero,
whole-track intertwining, exact-functor naturality, the inverse level-one formula and supplied
path evaluation. Generic stable operations and null evaluation retain all integer degrees;
stable interchange is stated in nonnegative degrees under the source Omega condition.
The supplied-null factorization and actual cone transition are proved. See [the complete
operation crosswalk](migration/native-self-track-operations.md).

## Actual scalar tracks and return-to-operation identification

COL-0324 constructs the raw and normalized scalar tracks, whole AsSmall path transport and
genuine flat-unit restriction. Arbitrary flat-morphism termwise pullback preserves native
perfectness and is Waldhausen exact on the same functor; the literal restriction isomorphisms
retain their original unitors. Finite restriction includes Pi-one and stable restriction retains
all integer degrees with its signs and canonical reindexing. The prescribed scalar return
equals the actual K-operation: the level-one inverse and return inverse cancel. The original
connecting map sends both raw and normalized operations to the positive canonical-fiber cone
image on every original subdivision cube, including n = 0. The scalar-cone relative canonical
null square and rotated prespectrum pasting are also constructed. See [the scalar-operation
crosswalk](migration/scalar-track-operation.md).

## Scalar-operation topic boundary

The generic operation and its actual scalar identification are complete at these precise
inputs. Arbitrary-input descent, subdivision coverage, global scalar boundary formulas,
the independent flat-unit canonical-null family and the object/row K-one applications remain
separate. A scalar-cone null square is not that independent flat-unit null family. Actual qcqs
roof/complement existence remains a separate geometric blocker, not a target of this topic.
The distinction between connective TT 5.1 and Bass nonconnective TT 7.4, and between the
relative positive signed cone and the T-first negative structure-sheaf convention, is unchanged.
No full TT localization, Bass formula, Nil vanishing or homotopy invariance is asserted.
Local compilation, component source/mathematical review, independent integrated review and
exact-tree remote lint, production axiom and Library checks are separate gates.


## Bounded Above Flat Perfect Comparison

COL-0323 and COL-0325 complete the genuine bounded-above flat perfect comparison.
The model uses termwise stalkwise-flat sheaves and native locally perfect complexes,
with an upper bound only, not finite amplitude or globally finite free terms. Its
inherited exact/Waldhausen structure uses actual quotient cofibrations and
quasi-isomorphisms, constructed joint cylinders and the literal inclusion into
native perfect complexes. The strict-to-flat-to-perfect composite is the original
strict inclusion.

Relative bounded-above projective factorization, exact sheafification and the native
counits construct the strict triangle and actual quasi-isomorphism with a genuinely
flat perfect quotient. This supplies App2 under CompactSpace alone. The canonical
K-map of the literal inclusion is bijective in every natural degree, including zero,
and is the forward map of the group equivalence. COL-0325 discharges the relative
factorization and K-comparison obligations left open by COL-0323. See the individual
COL-0323 and COL-0325 Library entries and source crosswalks for exact statements.

Arbitrary bounded-flat morphism pullback, all-perfect transport, supported/relative
comparison and global open-pair localization naturality remain separate topics.
Actual qcqs geometric roof/complement existence remains blocked by native geometric
prerequisites. This does not obstruct the completed bounded-flat comparison.
TT 5.1 connective K0-image-cover localization and TT 7.4 Bass nonconnective localization
remain distinct; neither global localization nor the Bass theorem is claimed here.
Local compilation, independent integrated review and exact-tree remote checks are
separate validation gates.


## Arbitrary Perfect Pullback and Restriction Compatibility

COL-0322 constructs actual arbitrary scheme pullback of bounded finite locally free
complexes, inherited conflations and quasi-isomorphisms, and their original canonical
K-maps with identity, composition, vector-bundle compatibility and open-pair squares.
COL-0326 extends this to bounded-above stalkwise-flat locally-perfect complexes and
transports their genuine canonical K-map along the literal inclusion K-equivalence
to arbitrary perfect K-pullback. For a morphism X to Y only CompactSpace Y is needed;
there is no flatness, quasi-separatedness or resolution-property hypothesis.
Identity, composition and contravariant functors retain their actual comparison maps.

COL-0328 identifies this transported map with the independently constructed original
flat-morphism exact K-map, ordinary open restriction and open-subset maps, in every
natural degree including zero. Its literal-inclusion natural-isomorphism square
proves these identifications. The open-pair square needs compactness only on the
target scheme and target open, not on the source scheme or source open. The coarse
perfectOpenKRestrict map is compared only after composition with perfectOpenKMap;
it is not identified directly with fine perfect-complex restriction.

Supported/relative-pair maps, whole-prespectrum comparison, supported global
localization naturality, TT 5.1 image-cover geometry and Bass TT 7.4 remain separate.
The original source is Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
See COL-0322, COL-0326 and COL-0328 and their precise source crosswalks. Local
compilation, independent integrated review and remote publication are separate gates.


## Supported Relative-Open Coarse Fibration

COL-0331 provides native support restriction and the forward/coarse fibration
for any scheme, open immersion and arbitrary auxiliary open T. The literal fiber
has support outside the union of T and the open image. Canonical inclusion,
fiber, boundary and projection maps give all-natural-degree exactness, including
the coarse relative K0 tail, with target PerfectSupportedOpenCoarseK.
No qcqs or CompactSpace T assumption and no Aglib adapter is used.
See [the source crosswalk](migration/quillen/supported-open-coarse-fibration.md).
Opposite-exact auxiliary statements, prespectrum/stable/chosen-zero transport,
fine supported-open TT 5.1.2 and Bass remain separate, unclaimed topics.


## Supported-Cover Excision

COL-0332 adds supported-cover excision for an open immersion j and auxiliary open T with image(j) union T = X: genuine extension-by-zero adjunction, stalkwise exactness, supported perfectness by two-open descent, actual S-realization inverse, literal restriction K-equivalence including K0, and normalized connective prespectrum stability in every integer degree. No qcqs, compactness, separation or supplied-equivalence premise is used. Negative stable degrees are connective vanishing, not Bass. COL-0331 retains its coarse target and stated limitations; fine TT localization and opposite exactness remain unclaimed.
No Aglib or Quillen adapter is used. See [the exact source crosswalk](migration/quillen/supported-cover-excision.md).


## Native Qcqs Scheme Localization

COL-0307 proves actual perfect derived roofs and perfect complements for a quasi-compact quasi-separated scheme X and quasi-compact open U, allowing a quasi-coherent-cohomology target that need not be perfect and any chosen open derived model. COL-0330 uses these geometric results to establish fixed-pair TT Theorem 5.1.1: the actual coarse connective Omega spectrum realizes the K0 restriction-image cover, with positive-degree isomorphisms and exactly the K0 restriction image, together with actual supported fiber, projection, nullhomotopy, canonical rebase and boundary compatibility. COL-0332 supplies supported-cover excision under image(j) union T = X without compactness. Full additional-support TT 5.1.2, arbitrary global-pair naturality and Bass 7.4 remain separate and are not claimed.
See the [geometry crosswalk](migration/native-perfect-roofs.md), [fixed-pair endpoint crosswalk](migration/native-qcqs-connective-localization.md), and [supported-cover excision crosswalk](migration/quillen/supported-cover-excision.md). No additional preselected cover-spectrum comparison is required for this fixed-pair statement.

## Fixed-pair supported connective image cover (COL-0335)

The actual supported coarse S-prespectrum is now assembled as the connective image
cover for the fixed additional-support pair under qcqs ambient and compact-union
hypotheses. Literal union-support/acyclic transport preserves the original inclusion,
whole nullhomotopy, independent structure/time parameters, level-one fiber K-map and
all-integer stable equivalence. The original exact supported restriction factors
coherently through the coarse model, and COL-0334 supplies the positive comparison
and exact K-zero image. See [the source crosswalk](SUPPORTED_CONNECTIVE_IMAGE_COVER.md).
Support-forgetting boundary compatibility is handled separately by COL-0336 below.
Arbitrary global-pair naturality, general two-piece supported gluing and Bass TT 7.4
remain separate obligations.

The supporting components have separate source crosswalks: [supported qcqs geometry](migration/native-supported-qcqs-geometry.md) (COL-0333) and [supported fine comparison](migration/native-supported-fine-comparison.md) (COL-0334).

## Auxiliary-support forgetting (COL-0336)

The original supported positive inverse and fine boundary now commute with actual
support forgetting. All fixed-pair group-level localization squares retain their original
maps, supports and signs, explicitly including K1 to K0. The fine statements require
compact U and compact union; compact U/T gives the original corollaries. See
[the source correspondence](SUPPORT_FORGETTING_NATURALITY.md). Whole-prespectrum
nullhomotopy preservation remains a separate obligation, as do arbitrary pair
naturality and Bass localization.

## Whole-prespectrum support forgetting (COL-0337)

The actual auxiliary-support forgetting square now preserves the entire original
nullhomotopy, its canonical fiber lift and the signed stable boundary at every
stage and degree. Null time and structure time remain independent. Restriction
uses the constructed coherent zero-rebase homotopy, and original connective
K-maps, level-one fiber maps and the K1-to-K0 minus sign are retained. No
compactness is needed for this naturality. See [the source correspondence](SUPPORT_PRESPECTRUM_NATURALITY.md). This closes the whole-prespectrum seam left
by COL-0336; coefficient naturality, Bass iteration/telescopes and TT 7.4 remain
separate. No stable equivalence of support forgetting or full-target fine K0
inverse is asserted.

## Strict-square cone-loop foundation (COL-0338)

The actual reduced double cylinder, strict-square comparison, cone-loop functor and whole
canonical source-null naturality are native. Scalar-track seed naturality and finite
iteration of strict evaluation diagrams retain their explicit supplied-track/seed inputs.
See [the exact source crosswalk and exclusions](STRICT_SQUARE_BASS.md). Scheme coefficient
seeds, telescopes, nonconnective identifications and TT 7.4 are not included.
