# Arbitrary perfect K-pullback

This item continues COL-0322, COL-0323 and COL-0325 on their unchanged native objects and maps.
The original implementation is Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native Stacks revision is `5ed82d14634e8d9576bb844c7bd4e3da66d450e7` and Mathlib is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Objects and exactness

The full subcategory consists of original sheaf cochain complexes that are native locally
perfect, termwise bounded above, and flat in every degree. No lower bound, finite local
freeness, termwise quasicoherence or global projectivity is inserted.

For an arbitrary scheme morphism the actual termwise native module pullback preserves this
class. Native Stacks bounded-above flat complexes are K-flat. The actual K-flat pullback
preserves quasi-isomorphisms and transports local strictly perfect presentations, proving
perfectness of the actual pulled-back complex. Flat terms stay flat by stalkwise base change.
The upper bound stays unchanged since additive pullback preserves zero objects.

Inherited short exact sequences have a flat quotient in every degree. Stacks 0G6R therefore
preserves those sequences. This is not an assertion that arbitrary module pullback is exact.
The opens-site presentation is extracted from the native mixed-derived-tensor module without
importing that higher application. The native theorem is proved, rather than accepted as a
new exactness assumption. Exact functors preserve the actual admissible cofibrations and their
pushouts; the K-flat theorem preserves the original weak equivalences.

## Coherence and K-maps

Identity and composition are actual natural isomorphisms of the full chain functors, lifted
from the native module comparisons. The bounded-vector-bundle inclusion commutes on original
objects and chain maps. Only after these facts are proved are the canonical chosen-zero
normalized Waldhausen KMaps formed. Their equations include every natural degree, including zero.

The all-perfect K-map is the composite of the inverse literal comparison on Y, actual flat
K-pullback along f : X → Y, and the unchanged literal inclusion on X. Only Y must be
quasi-compact. The forward comparison on X does not require an inverse. Identity requires X
quasi-compact, and composition X → Y → Z requires Y and Z quasi-compact. On the full category
of quasi-compact native schemes these maps give a contravariant group-valued functor and the
literal flat inclusion gives a natural isomorphism. The bounded-vector-bundle comparison is
only a natural transformation; it is not asserted to be an equivalence.

The native derived-category pullback proves the K-flat chain-model facts. It is not identified
with an exact underived functor on the category of all perfect chain complexes. The all-perfect
K-map is the explicitly proved transport of an actual chain Waldhausen K-map.

## Original-source correspondence

- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlatPullback.lean`:
  arbitrary pullback preserves the actual bounded-above flat local-perfect predicate.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Pullback.lean`:
  actual chain functor and exactness via flat quotients.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/PullbackIsomorphisms.lean:35-48`:
  native identity and composition comparisons.
- `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Pullback.lean:45-61`:
  actual Waldhausen exactness.
- `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean:47-72,94-99`:
  canonical K-map, identity/composition, flat K-functor and strict-to-flat naturality.
- `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullback.lean`:
  literal-comparison transport, identity/composition and bounded-vector-bundle compatibility.
- `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullbackFunctor.lean`:
  contravariant K-functors and literal natural comparison.

## References and boundary

The exactness input is [Stacks 0G6R](https://stacks.math.columbia.edu/tag/0G6R), the flatness
input is [Stacks 0H97](https://stacks.math.columbia.edu/tag/0H97), K-flat pullback uses
[Stacks 06YC](https://stacks.math.columbia.edu/tag/06YC) and
[Stacks 06YJ](https://stacks.math.columbia.edu/tag/06YJ), and native local perfectness is
[Stacks 08CM](https://stacks.math.columbia.edu/tag/08CM) with pullback
[Stacks 09UA](https://stacks.math.columbia.edu/tag/09UA).

Supported pair comparison and full open-pair localization naturality are not established here.
Support continues to mean complexes on X supported on X minus U, not K-theory of the complement.
This item makes no claim about arbitrary scalar-input descent, TT5.1 image-cover closure or
Bass TT7.4. Source correspondence and local compilation are separate from independent review.
