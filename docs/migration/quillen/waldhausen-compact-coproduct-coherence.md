# Compact coproduct cubes and whole null coherence

COL-0302 records one complete compact-coproduct construction, not a milestone
for an isolated continuity or path helper. Implementation provenance is the
seven `Quillen/Waldhausen/Additivity/CompactCoproduct*.lean` files at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using bibliography key `quillen`.
The original copyright, author and Apache 2.0 notice remain on all adapted
production and regression files.

## Exact mathematical scope

Let `C : Type u` have `Category.{v} C`, with independent object and morphism
universes, and let `W` be its Waldhausen structure. The product lift does not
need binary coproducts. The coproduct constructions assume
`HasBinaryCoproducts C`. The actual input cubes are
`GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint`, for every `n : ℕ`.
In particular `n = 0` still has one spatial coordinate. The parameter space
is the original `T : Type`, with its topology and compactness assumptions.

The product lift is selected from the proved compact-source lifting theorem
for `Product.deloopingComparison W W`; projection injectivity proves
uniqueness, whole-face preservation and compatibility with concatenation.
Continuity is obtained by lifting the entire compact parameter/spatial
product together. It does not use a global inverse to product realization.
The coproduct uses the actual exact functor canonically rebased at the chosen
zero. Its two units are the original first/second zero embeddings conjugated
by that same rebasing isomorphism, then realized through their actual weak
natural-transformation cylinders.

The separation path starts at `coproductCube W n p q` and ends at
`GenLoop.transAt 0 q p`. It delays `p` into the second half and `q` into the
first, using reversed separation time, then applies the original unit paths.
The order is literally `q` followed by `p`; no group-class commutativity or
newly chosen path replaces it. Every compact-family parameter, separation
time and spatial coordinate survives. The entire cube boundary is fixed.

The unit square uses both independent times. The supplied-null square
contains the entire original path `N`, not merely its class. The original
square interpolation compares its four whole edges and produces
`coproductSeparationNullCoherence`; its full spatial boundary remains fixed
at every homotopy and path time.

For `NestedWeakEquivalences W`, the componentwise product enlargement has
the same cofibrations and chosen zero. The complete product lift, rebased
coproduct, unit cylinders, spatial delays and separation path commute with
the actual `changeWeakMap`. Whole-path equalities retain both endpoint
casts, and the mapped null retains its constant-target transport.

Finally, `CompactCoproductEndpoint.normalizedNullHomotopy` retains the
original `A0`, `T0`, `T1`, coarse null `N`, moving endpoint path `Z`, and
whole `Jtheta` homotopy as explicit inputs. It compares the original
normalized null to the mapped original fine delta followed by the entire
supplied null. Both inverse-prefix cancellations and all parentheses and
source casts remain. This is exactly the original conditional topological
endpoint: it neither manufactures `Jtheta` nor establishes the geometric
scalar forward relative boundary.

## Native objects and mathematical owners

The construction directly uses Mathlib `GenLoop`, `Path`, `ContinuousMap`,
relative path homotopies and the existing native Colib Waldhausen/realization
interfaces. Production imports no Quillen or Aglib package and introduces no
adapter model or theorem-shaped replacement premise. The pinned Mathlib and
Stacks dependency revisions are unchanged.

The seven high-level files retain their names under
`Colib.KTheory.Waldhausen.Additivity`. Their public declarations extend
`CategoryTheory.Waldhausen.Additivity` and its `CompactCoproductEndpoint`
namespace. Low-level declarations have separate mathematical owners:

- `Colib.CategoryTheory.Waldhausen.Additivity.RebasedCoproduct` contains the
  six actual rebasing/exactness/unit-isomorphism declarations from Units.
- `Colib.CategoryTheory.Waldhausen.Product.NestedWeakEquivalences` owns
  `Product.nestedWeakEquivalences`, the original componentwise enlargement.
- `Colib.Topology.Homotopy.HomotopyGroup.GenLoopUnitPaths` owns the original
  delays, endpoints, constant-track identities and actual right-unit path.
- `Colib.Topology.Homotopy.SquareEdges` owns `Topology.squareEdgeHomotopy`,
  the original generic four-edge interpolation.
- The unchanged `Colib.Topology.Realization.HomotopySquare` already provides
  `SSet.realizationSimplicialHomotopy_square`. The two calls use the symmetric
  commuting-square equality; no duplicate helper or API change is introduced.
- `Colib.Topology.Path.Homotopy.ThetaWord` owns the original generic
  `Path.Homotopy.removeSuffix` and `thetaWord` path calculations.

These are direct native definitions, not aliases or compatibility reexports.
The existing topology self-track, prefix/null-coherence and realization
naturality prerequisites were already present and are reused unchanged.

## Source correspondence and verification

All 120 original declarations are accounted for: 119 are retained across
the 12 production modules, and the private realization-square helper is
absorbed by the already existing native theorem. Native imports and namespaces
change; the product weak enlargement and two generic square helpers receive
names reflecting their mathematical owner. The original maps, hypotheses,
universes, coordinate order, path words, proof constructions and signs are
unchanged.
The complete per-declaration source/target crosswalk, original and target
source hashes, lexical namespaces and reuse relation are maintained in
[compact-coproduct-sources.json](compact-coproduct-sources.json).
Twenty-five final public declarations carry COL-0302 bindings
and exact original declaration-span references. Supporting declarations
retain source-file provenance without receiving independent milestone IDs.

Seven adapted in-package regression modules preserve the original checks
of projections, faces, exact paths, endpoint transports, entire null data,
whole spatial boundaries and one-coordinate inputs. Local validation uses
the pinned Lean 4.35 compiler, serializes compilation, and reuses only
providers whose source and complete direct-dependency artifact families
match. Changed leaves, regression modules, reverse consumers and the exact
aggregate root are the final compilation scope. Native lint, generated
Library validation and the production axiom audit belong to remote CI.
Author source correspondence, local elaboration, independent mathematical
review and exact-commit remote CI are separate evidence; this document does
not by itself certify any of the latter three.
