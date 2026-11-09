# Whole-prespectrum auxiliary-support forgetting (COL-0337)

## Source and native objects

Original source revision: `quillen` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The source comparison uses the actual original files, not an adapter model:

- `Quillen/Waldhausen/Fibration/Prespectrum.lean`: original change-weak map, acyclic
  inclusion, reversed whole zero-to-inclusion null, and specified path-space fiber lift.
- `Quillen/Waldhausen/Fibration/CanonicalFiberNaturality.lean`: strict chosen-zero
  delooping naturality. COL-0337 proves the genuinely stronger all-stage statement.
- `Quillen/Waldhausen/SConstruction/Iterated/PrespectrumHomotopyNaturality.lean`:
  actual iterated transformation pre/postcomposition, including the level-zero loops.
- `Quillen/Topology/Prespectrum/FiberLiftNaturality.lean` and `FiberNaturality.lean`:
  strict actual fiber square and its signed stable boundary, using the full null.
- `Quillen/Waldhausen/Fibration/StableConnectingComparison.lean`: the minus sign
  between the original K-theory boundary and the stable connecting map, with degree cast.
- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Forget.lean:30-92`:
  original coarse and union-support forgetting functors and connective boundary square.
  COL-0336 supplies the native exact functors and group maps; COL-0337 retains these
  exact maps on the entire original prespectrum.

Waldhausen's fibration theorem is the underlying fiber comparison (1985, Section 1.6,
Theorem 1.6.4 and its proof, pp. 350–352). The supported connective image-cover geometry
was established separately by COL-0333/0334/0335. It is not an input to raw naturality.

## Generic proof, with no null-compatibility premise

`Colib/KTheory/Waldhausen/Fibration/PrespectrumNaturality.lean` constructs the actual
fine, coarse and acyclic maps of the original iterated-S prespectra. Exactness for both
nested weak structures and literal chosen-zero preservation give the two strict squares.
Small-model postwhiskering and prewhiskering identify the actual zero-to-inclusion
transformations by uniqueness out of the zero object. Native transformation-homotopy
naturality then proves equality at every stage n and null time s. Reversal retains the
original null orientation. The separate structure time t is explicit in the exported
structure theorem. No supplied profile, replacement null or assumed hN is present.

The native `homotopyFiberLift_naturality` is applied only after this whole hN is proved.
The result retains source coordinates and every point of the fiber path. Signed stable
boundary naturality uses the native `stableFiberConnecting_naturality`.

## Scheme specialization and signs

`PerfectSupportedOpenForgetPrespectrum.lean` uses the COL-0336 exact inclusions,
preserving the native ambient zero literally. A strict flattening square identifies the
induced acyclic functor with union-support forgetting. Consequently the *specified*
supported null and actual supported fiber lift commute, not just their K-group maps.
No compactness, qcqs, surjectivity or stability of forgetting is assumed.

Coarse restriction uses canonically rebased exact-functor maps. Its square is therefore
an explicit coherent homotopy assembled from chosen-zero and composition homotopies,
not a false strict equality. The rebased supported fiber presentations are likewise
related by the actual coherent homotopies. The original level-one delooping maps and
existing supported fiber piMaps are retained; `originalKStableEquiv` identifies actual
connective coarse and union forgetting with their COL-0336 maps.

`PerfectSupportedOpenForgetStableBoundary.lean` inverts only the already-proved original
supported fiber lifts to define their intrinsic integer-graded stable boundaries.
The complete-null square proves their naturality. Explicit original K-comparison formulas
retain the minus sign and degree cast. The n = 0 formula is K1 to K0. Forgetting support
is generally not a stable equivalence, and no such premise is introduced.

## Consumer and boundary of the claim

`ColibTest/SupportedOpenForgetPrespectrum.lean` checks full signatures for arbitrary j,T:
strict inclusion/change-weak/flattening maps, every null time and stage, independent s,t,
actual fiber square/projection/path, rebase homotopies, the signed integer boundary,
original K-map and level-one identifications, and explicit K1-to-K0 signs and squares.
Generic abstract exact functors are also checked independently of the scheme instance.

This is a coherent connective-spectrum input toward Bass localization, not Bass completion.
Generic strict-square Bass iteration, coefficient functors and genuine prespectrum
telescopes remain subsequent constructions. Fine K0 remains the actual restriction image;
no full-target inverse or surjectivity is asserted. There are no Aglib or adapter imports.
Compilation, source correspondence and independent review are separate evidence.

In particular, TT Theorem 7.4 and arbitrary global-pair prespectrum naturality are not
claimed. Current verification compiles the changed production and consumer modules
and affected aggregates against the exact inherited native providers. Their existing
source and input/output artifact identities are retained; this is not a fresh replay of
all native dependencies. Historical dependency options remain historical, without a
retroactive claim that the standard linter set was enabled for every inherited producer.
New production uses the required standard-linter set and warnings-as-errors. Remote
lint, private catalog export and production transitive-axiom gates remain distinct from
these local compilation and source-correspondence checks.
