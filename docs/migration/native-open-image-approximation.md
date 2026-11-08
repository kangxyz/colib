# Relative restriction onto the honest derived image

COL-0314 completes the native strict incoming approximation application. Its only
geometric input is `OpenDerivedImage.HasDerivedRoofs j`: actual derived morphisms
between restrictions of global native perfect complexes admit the specified global
perfect model and locally quasi-isomorphic denominator. COL-0307 owns the eventual
proof of that exact property under the original qcqs hypotheses.

## Original source and actual objects

The source is Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, under
`Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/`:

- `Structure.lean:42-109`: literal opposite image structure and actual exactness.
- `JointComparison.lean:38-64`: canonical cross-category opposite cylinder comparison.
- `JointData.lean:28-35`: actual opposite weak-arrow joint data.
- `Approximation.lean:50-91`: strict incoming target lift and relative exactness.
- `Approximation.lean:95-119`: actual relative corestriction K-map bijectivity.
- `KTheory.lean:30-34`: literal factorization of the existing open restriction K-map.

The underlying objects are native Stacks perfect cochain complexes on the schemes,
and the honest image uses actual derived isomorphisms. Its category has one wrapper
around each original complex. All functors retain original chain maps. Cofibrations
in the unchanged fine and relative source are ambient monomorphisms.

## Discharged categorical obligations

The three forward endpoint equations additionally specialize the proved native generic
comparison; the original application source explicitly stated its three inverse equations.

The actual image cokernel and kernel remain in the image by the proved short-exact
closure. Thus exact-subcategory inflations and deflations are precisely ambient
monomorphisms and epimorphisms. This identifies the opposite structure with the
original forward structure without replacing its zero or cofiber choices.

The existing exact additive restriction supplies opposite exactness. The canonical
biproduct and identity-cone natural isomorphisms transport the common opposite
cylinders through the actual degree-reversing equivalences. Both endpoints and the
weak projection commute in both directions. No comparison of independently chosen
cofibers is asserted to be definitional equality.

These component cylinders and proved endpoint equations construct the actual
opposite weak-arrow joint data. The strict incoming factorization gives both
literal chain-map equations, degreewise split epimorphisms and both actual kernel
memberships. Those maps define the genuine weak-arrow target lift.

The generic dual inverse-image theorem applies to this constructed joint data and
these actual lifts. The actual weak-arrow diagonal/source equivalence transports
its conclusion to the unchanged relative corestriction K-map. No approximation,
joint compatibility, joint-data or K-equivalence premise is assumed.

## Exact conclusion and boundary

For every nonnegative degree, the actual relative corestriction K-map is bijective.
`relativeCorestrictKEquiv` is the induced multiplicative equivalence; its forward
function is literally that K-map. Composing with the actual image inclusion recovers
`perfectOpenKRestrict`, including degree zero.

This is conditional only on the exact geometric roof proposition, in addition to
the stated native category and open-immersion structures. It does not establish the
roof proposition, ordinary outgoing App2, a global reflection of quasi-isomorphisms,
qcqs localization, the complement/density step, or surjectivity onto all perfect K-zero
of the open. No Noetherianity, regularity, separatedness or resolution property is added.

Geometric and categorical constructions have no transitive KTheory import. The
approximation conclusion and canonical K-group equivalence have their separate
`Colib.AlgebraicGeometry.KTheory` owner.
