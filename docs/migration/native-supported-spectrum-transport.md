# Native supported-spectrum transport

## Mathematical statement

COL-0319 completes the actual supported-to-relative-coarse-fiber assembly left open by
COL-0318. For any open immersion `j : U ⟶ X`, support means that the original complex of
`X.Modules` is native Stacks-perfect and its actual restriction to U is acyclic. It does
not mean K-theory of the closed subscheme X minus U.

The two fine Waldhausen categories have a literal two-sided exact flattening. Both
inherit the same ambient zero complex, so the original zero-preserving S-prespectrum
maps are strict inverses. This proves an isomorphism of the original prespectra before
any homotopy-group comparison. It does not assert that canonically rebased functors
compose strictly.

Compose the supported-to-acyclic map with the original canonical acyclic fiber map.
Its projection is exactly the original supported inclusion, and every fiber path is
exactly the original acyclic nullhomotopy precomposed with that map. No replacement
nullhomotopy, chosen stable equivalence, group-level LES, or coherence premise is an
input. The nullhomotopy keeps both independent parameters, and commutes with each
original structure map at every time. The resulting actual map is a stable equivalence
in every integer degree by the proved prespectrum isomorphism and the native acyclic
fiber theorem.

The canonical zero-rebase isomorphism induces a coherent homotopy between normalized
and zero-preserving maps. Postcomposition produces that homotopy inside the same
homotopy fiber. Its projection coherently agrees with the normalized supported
inclusion. At level one, the entire supported fiber map agrees through the original
universe-transport homeomorphisms, including its path coordinate. The induced original
homotopy-group map is exactly the existing `perfectSupportedFiberKMap`, and stable
inclusion retains `perfectSupportedKMap`.

## Original-to-native crosswalk

The original source is Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Full-file Git blobs and the complete cited spans are checked in the component's source
correspondence evidence. Existing native prerequisites retain their own migration owners.

- `Quillen.PerfectComplexes.perfectSupportedToAcyclic` and
  `perfectAcyclicToSupported`, in `OpenSupport.lean:54-202`, become the already native
  `AlgebraicGeometry.Scheme.Modules` functors on actual Stacks-perfect complexes.
  Their original composites now induce `perfectSupportedAcyclicPrespectrumIso`.
- `Quillen.Waldhausen.IteratedS.originalPrespectrumMap_comp`, in
  `Waldhausen/SConstruction/Iterated/ExactCoherence.lean`, retains its native generic
  owner. Its actual strict chosen-zero composition proves the supported inclusion square.
- `originalPrespectrumTransformationHomotopy`, in
  `Waldhausen/SConstruction/Iterated/PrespectrumHomotopy.lean`, supplies the explicit
  `exactOriginalPrespectrumMapChosenZeroHomotopy` from the actual rebase isomorphism.
- `Quillen.Waldhausen.Fibration.canonicalFiberPrespectrumMap` and its source/path/
  projection theorems, in `Waldhausen/Fibration/Prespectrum.lean`, become the unchanged
  native canonical map. Its transport is `perfectSupportedFiberPrespectrumMap`.
- `canonicalFiberPrespectrumMap_level_one_square` and the all-integer stable theorem,
  in `Waldhausen/Fibration/SpectrumComparison.lean`, identify the actual level-one
  map and supply the already proved acyclic equivalence. The new transport and its
  canonical-rebase comparison do not assume that equivalence for support.
- `Quillen.PerfectComplexes.perfectSupportedFiberKMap`, in
  `OpenLongExactSequence.lean:39-81`, is the existing native group map. The new
  `perfectSupportedFiberMap_piMap` and level-one square prove that the actual spectrum
  map realizes it, rather than merely packaging its group-level bijectivity.

## Exact boundary

This assembly needs no roofs or perfect-complement existence. COL-0318 separately
proves that the relative coarse model has positive stable equivalences to fine K(U),
and stable degree zero equal to the global restriction image, under the accurate
`HasDerivedRoofs` and `HasPerfectComplements` geometric inputs. Their qcqs discharge
remains separate. No uncompiled perfect-roofs draft is imported here.

TT Section 5.1, printed pages 337–338, is connective proto-localization with the
image-corrected target; Section 5.2.2 describes the K-zero extension obstruction.
The present actual supported fiber assembly is a prerequisite for a full geometric
identification, not by itself a claim that all of TT 5.1 has been proved. Comparison
with a separately prescribed topological image-cover spectrum and global open-pair
naturality remain separate. Earlier derived-image membership reflection is not
silently reinterpreted as a topological covering construction.

TT Section 7.4, printed page 365, concerns Bass nonconnective K-theory of ambient X
with support away from U. Integer-graded stable equivalence of the present connective
spectra is not that theorem. Existing relative-boundary and T-first Bass sign
conventions are unchanged.

## Owners and validation

`Iterated/ChosenZeroCoherence` owns the generic chosen-zero comparison.
`PerfectSupportedPrespectrum` owns the actual support/fiber assembly, and
`PerfectSupportedFiberComparison` owns the original-level and rebased comparisons.
`ColibTest.PerfectSupportedPrespectrum` checks complete signatures, actual path and
structure coordinates, independent generic universes, stable equivalences, and original
K-map identification. Source compilation, source correspondence, independent mathematical
review and integrated CI are distinct facts. Shared root, chapter and migration-index
changes are proposed to the integration owner, not edited in this component.
