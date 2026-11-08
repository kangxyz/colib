# Prescribed canonical-fiber component translation: COL-0296

This complete endpoint adapts the specified construction at Quillen commit
[`c561118b7795eb9780be9ed391c3251d6a4d0afd`](https://github.com/kangxyz/quillen-k-theory/tree/c561118b7795eb9780be9ed391c3251d6a4d0afd).
It includes both genuine homotopy equivalences and their literal values on the
original canonical-fiber object loop. Independent source and mathematical/API
review established source correspondence before native compilation. The integrated
sources and tests subsequently passed the native CI recorded below.

## The actual equivalences and their hypotheses

Let `{C : Type u} [Category.{v} C]`, `V : Structure C`,
`N : NestedWeakEquivalences V`, and `A : C`. Write

- `g = basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)`;
- `alpha = V.kZeroObjectLoop A`, `gamma = N.coarse.kZeroObjectLoop A`;
- `e = Path.refl N.coarse.kBasepoint` and `HF(g,b) = HomotopyFiber g b`.

The strict square `L_gamma.comp g = g.comp L_alpha` uses the actual object-loop
naturality law and genuine left-concatenation equivalences. It gives
`canonicalFiberPrefixEquiv N A : HF(g,e) ≃h HF(g,gamma.trans e)` with forward map
`(delta,beta) ↦ (alpha.trans delta, s ↦ gamma.trans (beta s))`.
This construction and its literal object-value theorem need no zero-morphism
instance.

With `[HasZeroMorphisms C]`, let `sigma = N.coarse.identityCofiberSuffixPath A`.
This specified path runs from `gamma.trans e` to `gamma`. Appending exactly
`sigma` gives `canonicalFiberComponentEquiv N A : HF(g,e) ≃h HF(g,gamma)`.
Its definition is the prefix equivalence followed by
`HomotopyFiber.basepointTransportEquiv g sigma`.

These are fibers of the original **based loop map**, not connected-component
subspaces or fibers of the delooping map. The object `A` is arbitrary and need
not be acyclic or nonzero. The target is its specified coarse object loop, not
an arbitrary target loop. Both category universes remain independent; the
relevant delooping spaces have universe `max u v`. Neither result assumes
`SmallCategory`, joint-cylinder data, a fibration theorem, connectivity, or
weak equivalence of `canonicalFiberMap`. The strict translation step requires
no path from `e` to `gamma`; only the suffix step is basepoint path transport.

## The complete original point and prescribed suffix

For `X : AcyclicCategory N`, `canonicalFiberObjectLoop N X` is the actual
based loop map of `canonicalFiberMap N` applied to the inherited object loop.
Its fine source is `V.kZeroObjectLoop X.obj`. At independent loop time `t` and
fiber time `s`, its stored coordinate is
`acyclicNullhomotopy N (s, (acyclicStructure N).kZeroObjectLoop X t)`.
That nullhomotopy is the whole original zero-to-inclusion homotopy reversed
in **fiber time**. The inverse `loopFiberHomeomorph` transposes the coordinates
without another reversal.

The prefixed source is literally `alpha.trans (V.kZeroObjectLoop X.obj)`.
At `(s,t)`, the prefixed stored path is `gamma(2*t)` for `t ≤ 1/2`, and the
original canonical-fiber coordinate at `(2*t-1,s)` otherwise, with the source's
interval witnesses. Suffix transport concatenates this **whole** path with
`sigma` in fiber time, leaving the fine source unchanged. The exact point laws are

- `canonicalFiberPrefixEquiv N A (canonicalFiberObjectLoopTranspose N X) =
  canonicalFiberObjectPrefixed N A X`;
- `canonicalFiberComponentEquiv N A (canonicalFiberObjectLoopTranspose N X) =
  canonicalFiberObjectPrefixTransport N A X`.

The suffix is the actual identity-cofiber triangle for `(id A, A → 0)`.
The supporting row has interval entries `(0,A,B,0,Q,0)` in the order
`(00,01,02,11,12,22)`, the displayed arrows `i,q`, and literal zero arrows
elsewhere. Its faces `(d0,d1,d2)` are `(Q,B,A)`. The triangle composes the source
loop followed by the quotient loop to the middle loop. It uses the specified
characteristic map, affine weights `1-r,r`, and original endpoint casts.
The identity specialization gives exactly `sigma`, not a chosen homotopy witness
or generic right-unit path. No Laurent boundary or boundary-sign normalization
is asserted.

## Exact source crosswalk

Original paths below are relative to the pinned Quillen root; native paths are
relative to this repository. Whole-file coverage means all mathematical
declarations, not duplication of historical imports.

| Native owner | Original source and selected declaration span |
| --- | --- |
| `Colib/Topology/Realization/TriangleHomotopy.lean` | `Quillen/Topology/ClassifyingSpace/ArrowPaths.lean:146-212`: only the two data-valued homotopy definitions and composition application law |
| `Colib/CategoryTheory/Waldhausen/Rows/CofiberTwoRow.lean` | `Quillen/Waldhausen/SConstruction/Rows/CofiberTwoRow.lean:28-212`: whole mathematical content, including six private proofs; plus only `cofiberTwo_identity_square` from `Quillen/Waldhausen/SConstruction/Rows/CofiberTwoComparison.lean:93-98` |
| `Colib/CategoryTheory/Waldhausen/Rows/CofiberTwoFaces.lean` | `Quillen/Waldhausen/SConstruction/Rows/CofiberTwoFaces.lean:26-54`: whole mathematical content |
| `Colib/KTheory/Waldhausen/GrothendieckComparison/CofiberObjectTrack.lean` | `Quillen/Waldhausen/GrothendieckComparison/CofiberObjectTrack.lean:30-62`: whole mathematical content |
| `Colib/KTheory/Waldhausen/GrothendieckComparison/IdentityCofiberSuffix.lean` | `Quillen/Waldhausen/Fibration/IdentityCofiberComponent.lean:32-60`: only `identityCofiberSuffixPath` and its application law |
| `Colib/KTheory/Waldhausen/Fibration/CanonicalFiberObjectLoop.lean` | `Quillen/Waldhausen/Fibration/CanonicalFiberObjectLoop.lean:32-50`: the object loop and its two coordinate laws; `Quillen/Waldhausen/Fibration/CofiberPrismLeftPrefix.lean:28-49`: the transpose and its three laws |
| `Colib/KTheory/Waldhausen/Fibration/CanonicalFiberObjectPrefixTransport.lean` | `Quillen/Waldhausen/Fibration/CanonicalFiberObjectPrefixTransport.lean:31-93`: all six declarations |
| `Colib/KTheory/Waldhausen/Fibration/CanonicalFiberComponentTranslation.lean` | `Quillen/Waldhausen/Fibration/CanonicalFiberComponentTranslation.lean:31-94`: all five declarations |

The selected declarations retain the original maps and proofs after native
namespace/import changes, the existing affine primitive's native name, and
qualification of `Prod.ext`. Apache licensing and source authorship remain.
This is not a whole-file migration of the partially selected sources. The
weak-object/transformation tracks, weak-row comparison/prism/cube branch and
identity-component homotopy-group naturality package are separate work.

## References and registration

The endpoint's precise `colib_ref` uses existing key `quillen`, locator
`Quillen/Waldhausen/Fibration/CanonicalFiberComponentTranslation.lean:31-94`,
and relation `adaptation`. This source supplies the actual prefix, prescribed
suffix and literal point formulas; no inspected classical theorem prints this
entire statement.

Waldhausen, Section 1.3, definition of `S_n C` and face maps, pp. 328-329,
is an `ingredient` citation only for the lower literal row and face declarations.
It does not identify the affine suffix or final fiber-point equality.
Thomason--Trobaugh, Sections 1.8.1-1.8.2, p. 263, is optional background for
the chosen zero-to-acyclic nullhomotopy; its localization hypotheses and fiber
sequence conclusion are not imported into this endpoint.

COL-0296 binds the two equivalences and their two object-value laws. The strict
square is cited but remains untagged, as do lower supporting declarations.
`author_checked` records source correspondence, not compilation or CI status.

## Validation boundary

The slice consists of eight production leaves with 37 public declarations and
six private row proofs. Two focused test leaves contain 69 prepared regression statements
(28 lower assertions and 41 endpoint assertions), covering literal geometry,
independent universes/times, the zero-morphism split and both complete point
identities.
Source/static checks and independent source/mathematical reviews found no
blocker in the selected construction. Those checks are not Lean elaboration.

At the earlier preparation stage, the new leaves, tests and proposed attributes
had no native compilation evidence; prior baseline CI did not cover this slice.

The integrated sources and tests at
[`ea4dc640a5bec4e7eb49e0268c08c9f1fed1fc01`](https://github.com/kangxyz/colib/commit/ea4dc640a5bec4e7eb49e0268c08c9f1fed1fc01)
passed the repository's native checks in
[CI run 42435539991](https://github.com/kangxyz/colib/actions/runs/42435539991):
the `Build` and `Test, lint and axiom audit` jobs both succeeded. This
supersedes the uncompiled preparation status. `author_checked` continues to record source
correspondence only; independent mathematical review retains its own evidence
and checked span. No kernel-replay pass is claimed.
