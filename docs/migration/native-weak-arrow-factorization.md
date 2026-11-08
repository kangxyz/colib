# Native comma and weak-arrow factorization

## Mathematical scope

COL-0309 constructs the literal comma category `Comma F (𝟭 D)` and the full
subcategory of its objects whose stored arrow is weak. The source and target
projections, identity-arrow diagonal, counit and comparison retain the original
functors and actual stored arrows. Exactness follows from genuine component
pushouts, not a replacement diagram or an extra preservation hypothesis.

The diagonal and source induce mutually inverse canonical KMaps in every
nonnegative degree. The target KMap composed with the diagonal equivalence is
the unchanged KMap of F. Its bijectivity is equivalent to target bijectivity.
This is a first-leg result and does not prove the second-leg approximation.

Relative structures leave these fine weak-arrow objects, cofibrations, zero
and functors unchanged. Their weak map classes are detected through the actual
G or F followed by G. Final-target two-out-of-three proves relative source
exactness and the same diagonal K-equivalence.

Opposite comma pushouts arise from genuine component pullbacks. The inherited
opposite full-subcategory structure retains literal objects and component map
classes. Compatible duality uses actual zero-corner kernel/cokernel squares.
The two opposite weak-arrow projections jointly detect every actual pushout,
without a cofibration premise. Their zero and binary-coproduct detection retain
the original component universal properties.

## Source correspondence

The implementation source is Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Every original declaration and proof
in the following nine files is retained after the native namespace and import
moves. Public endpoint citations record exact original declaration lines.

| Quillen source under `Quillen/Waldhausen/` | Native owner under `Colib/` |
| --- | --- |
| `CommaCategory/Structure.lean` | `CategoryTheory/Waldhausen/CommaCategory/Structure.lean` |
| `CommaCategory/DualStructure.lean` | `CategoryTheory/Waldhausen/CommaCategory/DualStructure.lean` |
| `CofibrationClosedSubcategory/Opposite.lean` | `CategoryTheory/Waldhausen/CofibrationClosedSubcategory/Opposite.lean` |
| `WeakArrow/Structure.lean` | `CategoryTheory/Waldhausen/WeakArrow/Structure.lean` |
| `WeakArrow/KEquivalence.lean` | `KTheory/Waldhausen/WeakArrow/KEquivalence.lean` |
| `WeakArrow/RelativeStructure.lean` | `CategoryTheory/Waldhausen/WeakArrow/RelativeStructure.lean` |
| `WeakArrow/RelativeKEquivalence.lean` | `KTheory/Waldhausen/WeakArrow/RelativeKEquivalence.lean` |
| `WeakArrow/DualStructure.lean` | `CategoryTheory/Waldhausen/WeakArrow/DualStructure.lean` |
| `WeakArrow/DualDetection.lean` | `CategoryTheory/Waldhausen/WeakArrow/DualDetection.lean` |

The relative category construction no longer imports K-theory or duality,
which its statements and proofs do not use. Its K-equivalence module explicitly
imports native KMap functoriality. Compatible duality is the same native
`IsCompatibleDual` from COL-0308, not a second definition. The existing native
cofibration-closed-subcategory and inverse-image-weak constructions are reused.
The opposite-subcategory module imports native adjunction/limit preservation
explicitly, replacing the corresponding accidental transitive import.

## Hypotheses and boundary

Categorical structures retain independent object/hom universes for each
category. K-group statements retain the original `Type (max u v)` object
universe and hom universe v. No strict preservation of chosen zeros is assumed:
native KMap functoriality retains canonical zero rebasing.

Target reflection uses the original functor's weak reflection and target
two-out-of-three. Relative source exactness uses final-target two-out-of-three.
The dual weak-arrow closure uses exactness of the actual F.op and compatibility
of target weak classes; full dual compatibility also uses source compatibility.
No conclusion is moved into a new premise.

This supplies generic inputs for later localization work. It does not provide
WeakArrow JointFunctor/Endpoints/Exact/Data, opposite complex cylinders, target
approximation, or any qcqs-scheme fine localization theorem. No nonconnective
K-theory conclusion is claimed.

## Validation ownership

`ColibTest/WaldhausenWeakArrow.lean` checks the literal categories, stored maps,
relative weak predicates, independent universes, exact projections, opposite
component detection, and actual canonical KMap factorization in every degree.
Author source correspondence, local Lean compilation, independent mathematical
review, and remote lint/axiom audit remain distinct validation facts.
